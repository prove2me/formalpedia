-- Prove2me | Theorems.Thm_NCPComm_claim_3_7
-- name    : NCPComm.claim_3_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:03:19.324886+00:00
-- url     : https://prove2.me/theorems/e3bd63b7-a563-4a0c-85fa-7212a252f056
-- title:
--   Claim 3.7 — Poissonized counts
-- statement:
--   Let $D$ be a distribution over $[N]$, draw $s'\sim\mathrm{Poi}(s)$ and then $s'$ independent samples from $D$. The occurrence counts $X_x$, $x\in[N]$, are independent with $X_x\sim\mathrm{Poi}(sD(x))$.
--
--   Let $n$ labels each have probability $p$, let $h_i$ count those occurring exactly $i$ times, and let $q_i:=e^{-sp}(sp)^i/i!$. Then
--
--   1. $(h_i)_{i\ge0}$ is multinomial with $n$ trials and probabilities $q_i$;
--   2. $h_i\sim\mathrm{Bin}(n,q_i)$;
--   3. for $i\ge1$, conditionally on $(h_j)_{j\ge1,j\ne i}$, the count $h_i$ is $\mathrm{Bin}\big(n-\sum_{j\ge1,j\ne i}h_j,\ q_i/(q_0+q_i)\big)$.
--
--   Count vectors of disjoint sets of labels are independent. Finally, for every positive integer $r$,
--   $$
--   \Pr[s'<s/2]\le e^{-s/8},\qquad \Pr[s'>2s]\le e^{-s/3},\qquad \mathbb E\Big[\binom{X_x}{r}\Big]=\frac{(sD(x))^r}{r!}.
--   $$
--
--   This is the toolkit from which every law of the paper's analysis is computed.
--
--   **Formalization Note** Laws are stated by their point masses, and independence and conditioning as product formulas.
--
--   Differences from the source:
--   - encoding: labels in [N] = {1,…,N} → Fin N, 0-based; reason: Lean convention; same objects
--   - encoding: conditional law of h_i given (h_j)_{j≥1, j≠i} → Pr[h_i = k, others = w] = Pr[others = w]·Bin(…)(k), with others setting the entries 0 and i to 0; reason: the product form of a conditional law; it also holds where the conditioning event is null
--   - encoding: multinomial law of (h_i)_{i≥0} → point mass at every histogram supported in {0,…,m−1} with total n, for every m; reason: finite support is forced by a finite label set
-- source:
--   Herman, The Communication Complexity of Verifying Distribution Properties, STOC 2027 submission (manuscript sha256 714c0353…), Claim 3.7, p.15

import Mathlib
import Definitions.Def_NCPComm_idealSetup

open scoped NNReal ENNReal Topology
open Filter

namespace NCPComm

/-- **Claim 3.7 (Poissonized counts), p.15** (Herman, The Communication Complexity of Verifying
Distribution Properties, STOC 2027 submission, manuscript sha256 714c0353…).

For a distribution `D` over `[N]` and a Poissonized sample of mean `s`, with `law` the law of the
occurrence counts, and `S` a set of `n` labels of common probability `p` with `q i = e^{-sp}(sp)^i/i!`
and histogram `(h_i)_{i ≥ 0}` on `S`:
1. the counts are independent with `X_x ∼ Poi(sD(x))`;
2. `(h_i)_{i ≥ 0}` is multinomial with `n` trials and probabilities `q_i`;
3. `h_i ∼ Bin(n, q_i)`;
4. for `i ≥ 1`, `h_i` given `(h_j)_{j ≥ 1, j ≠ i}` is `Bin(n - ∑ h_j, q_i/(q_0 + q_i))`;
5. count vectors of disjoint label sets are independent;
6. the two Poisson tail bounds and the factorial moment.

**Formalization Note** Each law is stated by its point masses, with conditioning written as a
product. A histogram is a function `ℕ → ℕ`; a multinomial point mass is stated for every histogram
supported in `{0, …, m-1}`, for every `m`. -/
theorem claim_3_7 {N : ℕ} (D : PMF (Fin N)) (s : ℝ≥0) :
    let law : PMF (Fin N → ℕ) := (poissonSample D s).map countVec
    (∀ k : Fin N → ℕ, law k = ∏ x, poissonLaw (s * (D x).toNNReal) (k x)) ∧
    (∀ (S : Finset (Fin N)) (p : ℝ≥0), (∀ x ∈ S, D x = p) →
      let q : ℕ → ℝ := fun i => Real.exp (-((s : ℝ) * p)) * ((s : ℝ) * p) ^ i / (i.factorial : ℝ)
      let hist : (Fin N → ℕ) → ℕ → ℕ := fun c i => (S.filter fun x => c x = i).card
      let histLaw : PMF (ℕ → ℕ) := law.map hist
      (∀ (m : ℕ) (h : ℕ → ℕ), (∀ i, m ≤ i → h i = 0) → ∑ i ∈ Finset.range m, h i = S.card →
        histLaw h = ENNReal.ofReal ((Nat.multinomial (Finset.range m) h : ℝ) *
          ∏ i ∈ Finset.range m, q i ^ h i)) ∧
      (∀ i k : ℕ, (histLaw.map fun h => h i) k = binomialMass S.card (q i) k) ∧
      (∀ (i : ℕ), 1 ≤ i → ∀ (k : ℕ) (w : ℕ → ℕ),
        let others : (ℕ → ℕ) → ℕ → ℕ := fun h j => if j = 0 ∨ j = i then 0 else h j
        (histLaw.map fun h => (h i, others h)) (k, w) =
          (histLaw.map others) w *
            binomialMass (S.card - ∑' j, w j) (q i / (q 0 + q i)) k)) ∧
    (∀ S T : Finset (Fin N), Disjoint S T → ∀ (u : S → ℕ) (v : T → ℕ),
      (law.map fun c => ((fun x : S => c x), (fun x : T => c x))) (u, v) =
        (law.map fun c => fun x : S => c x) u * (law.map fun c => fun x : T => c x) v) ∧
    (poissonLaw s).toOuterMeasure {k | (k : ℝ) < (s : ℝ) / 2}
      ≤ ENNReal.ofReal (Real.exp (-(s : ℝ) / 8)) ∧
    (poissonLaw s).toOuterMeasure {k | 2 * (s : ℝ) < (k : ℝ)}
      ≤ ENNReal.ofReal (Real.exp (-(s : ℝ) / 3)) ∧
    (∀ (x : Fin N) (r : ℕ), 1 ≤ r →
      ∑' c : Fin N → ℕ, law c * ((c x).choose r : ℝ≥0∞) =
        ENNReal.ofReal (((s : ℝ) * (D x).toReal) ^ r / (r.factorial : ℝ))) := by sorry

end NCPComm
