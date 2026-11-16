-- Prove2me | Theorems.Thm_GoldProxGap_Supplement_theorem_6_10
-- name    : GoldProxGap.Supplement.theorem_6_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:48:32.043818+00:00
-- url     : https://prove2.me/theorems/5e2faeac-70f9-4c47-9d2f-90403f21c398
-- title:
--   Theorem 6.10 — decision-tree construction at rate $1/2$: $\Omega_h(\min\{N^{2^h-h-1},q/N\})$ exceptional challenges at agreement $(1/2+2^{-h-1})N$
-- statement:
--   **Theorem 6.10 (Decision-tree construction at rate 1/2).** Let $\mathbb F$ be a finite field of characteristic two, $D\subseteq\mathbb F$ binary additive of size $N=2^d$, $q=|\mathbb F|>N$, and fix $h\ge3$ with $d\ge2^h-1$. Put $K=N/2$ and $w=N/2^{h+1}$, and let $M=M_h(d)$ be the count of Lemma 6.9. Then
--
--   $$
--   M_h(d)=\Theta_h\bigl(N^{2^h-h-1}\bigr),
--   $$
--
--   and there is one received pair with
--
--   $$
--   \mathrm{CA}_K(f,g)=\mathrm{agr}_K(g)=K,\qquad \mathrm{agr}_K(f)\le K+w-1,
--   $$
--
--   and a set of at least $\min\{M/2,\ q/N\}$ distinct nonzero exceptional challenges at agreement $K+w=(1/2+2^{-h-1})N$. More precisely, the count is at least
--
--   $$
--   Z(M,F_{\mathrm{col}})=\max\Bigl\{M-\Bigl\lfloor\frac{F_{\mathrm{col}}}{q-N}\Bigr\rfloor,\ \Bigl\lceil\frac{(q-N)M^2}{(q-N)M+2F_{\mathrm{col}}}\Bigr\rceil\Bigr\},\qquad F_{\mathrm{col}}=\frac12\Bigl[\Bigl(K-w-\frac{K^2}{N-w}\Bigr)M^2+wM\Bigr],
--   $$
--
--   the bound (6.2) (the paper calls $F_{\mathrm{col}}$ simply $F$).
--
--   At rate $1/2$ the Johnson agreement is $N/\sqrt2$; the theorem gives polynomially many exceptional challenges, of degree $2^h-h-1$ in $N$, at agreement $1/2+2^{-h-1}$, on every binary additive domain.
--
--   **Formalization Note** $D$ is an additive subgroup of $\mathbb F$ of cardinality $2^d$. $M_h(d)$ is the value of the recurrence of Lemma 6.9 (`GoldProxGap.Supplement.treeM`). The $\Theta_h$ claim is stated with constants $c_1,c_2>0$ depending only on $h$, valid for every $d\ge2^h-1$. $K$ and $w$ are exact natural numbers; $M$, $F_{\mathrm{col}}$ and $Z$ are real numbers.
--
--   Differences from the source:
--   - reading: M = M_h(d), the count of Lemma 6.9 (the number of W-avoiding height-h tree functions) → M = treeM h d, the value of Lemma 6.9's recurrence; reason: Lemma 6.9 proves the count equals the recurrence, and the theorem uses only the number
--   - reading: M_h(d) = Θ_h(N^{2^h−h−1}) → ∃ c₁ c₂ > 0 (depending only on h) with c₁ N^{2^h−h−1} ≤ M_h(d) ≤ c₂ N^{2^h−h−1} for every d ≥ 2^h − 1; reason: M_h(d) > 0 for every admissible d, so the asymptotic and the uniform readings coincide
--   - reading: min{M/2, q/N} = Ω_h(min{N^{2^h−h−1}, q/N}) → not a separate conjunct; reason: it follows from the lower bound min{M/2, q/N} and the Θ_h conjunct
--   - encoding: the real number F of (6.2) → Fcol; reason: F already names the field
--   - encoding: D ⊆ F binary additive of size N = 2^d → D₀ : AddSubgroup F with Nat.card D₀ = 2^d, F a finite field with CharP F 2; reason: in characteristic two the additive subgroups are exactly the F₂-subspaces
--   - reading: one received pair … and at least min{M/2, q/N} … More precisely, the count is at least Z(M, F) → one pair and one set S of nonzero challenges with K + w ≤ agr_K(f + z g) on S, |S| ≥ min{M/2, q/N} and |S| ≥ Z(M, Fcol); reason: both bounds describe the same count
-- source:
--   Dao, Kominers, Thaler, Zheng, Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields, STOC 2027 submission manuscript (2 November 2026, sha256 6c2d9ced…), Theorem 6.10, p.56; eq. (6.2), p.51; Lemma 6.9, p.55

import Mathlib
import Definitions.Def_GoldProxGap_reedSolomon
import Definitions.Def_GoldProxGap_domainFinset
import Definitions.Def_GoldProxGap_Supplement_treeM

open Polynomial

open scoped Classical

namespace GoldProxGap.Supplement

/-- **Theorem 6.10 (Decision-tree construction at rate 1/2)**, p.56. Dao, Kominers, Thaler,
Zheng, *Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields*, STOC 2027
submission manuscript (2 November 2026, sha256 6c2d9ced…).

"Let D ⊆ F be binary additive of size N = 2^d, let q = |F| > N, and fix h ≥ 3 with
d ≥ 2^h − 1. Put K = N/2 and w = N/2^{h+1}, and let M = M_h(d) = Θ_h(N^{2^h−h−1}) be the count
of Lemma 6.9. There is one received pair with CA_K(f, g) = agr_K(g) = K, agr_K(f) ≤ K + w − 1,
and at least min{M/2, q/N} = Ω_h(min{N^{2^h−h−1}, q/N}) distinct nonzero exceptional challenges
at agreement K + w = (1/2 + 2^{−h−1})N. More precisely, the count is at least Z(M, F) of (6.2)
with F = (1/2)[(K − w − K²/(N − w))M² + wM]; Section 6.4 evaluates this bound."

**Formalization Note.**
* `F` is a finite field of characteristic two and `D = D₀ : AddSubgroup F` with `|D₀| = 2^d`
  (a binary additive domain, Definition 3.7), `N = 2^d < q = |F|`.
* `M = treeM h d`, the count `M_h(d)` given by the recurrence of Lemma 6.9 (see the definition
  module); the `Θ_h` claim is the first conjunct, with constants `c₁, c₂ > 0` depending only on
  `h` and valid for every `d ≥ 2^h − 1`. The `Ω_h` form of the count follows from it and the
  bound `min{M/2, q/N}`.
* The paper's real number `F` of (6.2) is renamed `Fcol` (it is not the field):
  `Fcol = (1/2)[(K − w − K²/(N − w))M² + wM]` and
  `Z(M, Fcol) = max{M − ⌊Fcol/(q − N)⌋, ⌈(q − N)M²/((q − N)M + 2·Fcol)⌉}`, in `ℝ`.
* `K = N/2`, `w = N/2^{h+1}` are exact natural numbers (`d ≥ 2^h − 1 ≥ h + 1`).
* "One received pair … and at least … distinct nonzero exceptional challenges" is one pair and one
  set `S` of nonzero challenges with `K + w ≤ agr_K(f + z g)` for `z ∈ S`, and both lower bounds
  on `|S|`. -/
theorem theorem_6_10 (h : ℕ) (hh : 3 ≤ h) :
    (∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ d : ℕ, 2 ^ h - 1 ≤ d →
      c₁ * ((2 : ℝ) ^ d) ^ (2 ^ h - h - 1) ≤ treeM h d ∧
        treeM h d ≤ c₂ * ((2 : ℝ) ^ d) ^ (2 ^ h - h - 1)) ∧
    ∀ (F : Type) [Field F] [Fintype F] [CharP F 2] (D₀ : AddSubgroup F) (d : ℕ),
      Nat.card D₀ = 2 ^ d → 2 ^ d < Fintype.card F → 2 ^ h - 1 ≤ d →
      let N : ℕ := 2 ^ d
      let q : ℝ := Fintype.card F
      let K : ℕ := N / 2
      let w : ℕ := N / 2 ^ (h + 1)
      let M : ℝ := treeM h d
      let Fcol : ℝ := (1 / 2 : ℝ) *
        (((K : ℝ) - w - (K : ℝ) ^ 2 / ((N : ℝ) - w)) * M ^ 2 + (w : ℝ) * M)
      let Z : ℝ := max (M - (⌊Fcol / (q - N)⌋ : ℝ))
        (⌈(q - N) * M ^ 2 / ((q - N) * M + 2 * Fcol)⌉ : ℝ)
      let Dom : Finset F := domainFinset D₀
      ∃ f g : Dom → F,
        CA Dom K f g = K ∧ agr Dom K g = K ∧ agr Dom K f ≤ K + w - 1 ∧
        ∃ S : Finset F, (0 : F) ∉ S ∧ (∀ z ∈ S, K + w ≤ agr Dom K (f + z • g)) ∧
          min (M / 2) (q / N) ≤ (S.card : ℝ) ∧ Z ≤ (S.card : ℝ) := by sorry

end GoldProxGap.Supplement
