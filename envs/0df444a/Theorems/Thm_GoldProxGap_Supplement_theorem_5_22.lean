-- Prove2me | Theorems.Thm_GoldProxGap_Supplement_theorem_5_22
-- name    : GoldProxGap.Supplement.theorem_5_22
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T03:48:02.584108+00:00
-- url     : https://prove2.me/theorems/ca1ebfae-868f-44cd-be1a-b92ec332b331
-- title:
--   Theorem 5.22 — quadratic-form families on full fields and hyperplanes, in every characteristic
-- statement:
--   **Theorem 5.22 (Quadratic-form families on full fields and hyperplanes).** Let $b$ be a prime power, $m=2n$, and $\mathbb B=\mathbb F_{b^m}$, with $\mathbb F_b\subseteq\mathbb B$ its subfield of size $b$. Let $D=\mathbb B$ or an $\mathbb F_b$-hyperplane in $\mathbb B$, and write $d=\dim_{\mathbb F_b}D$, $h=m-d\in\{0,1\}$ and $N=b^d$. Choose $2\le t\le n-h$, and put
--
--   $$
--   K=\frac N{b^2},\qquad T=\frac Nb-\frac{(b-1)N}{b^{t+1}},\qquad L=b^{2t}\,\frac{b^t-1}{b-1}\begin{bmatrix}n-h\\ t\end{bmatrix}_{b^2},\qquad \delta=\frac{(b-1)N}{b^{2t}} .
--   $$
--
--   1. There is a received word $w:D\to\mathbb B$ with at least $L$ distinct codewords of $C_K(D;\mathbb B)$, each agreeing with $w$ on **exactly** $T$ coordinates.
--   2. For every finite extension $\mathbb F\supseteq\mathbb B$ with $q=|\mathbb F|>N$ there is one received pair $f,g$ over $\mathbb F$ with
--   $$
--   \mathrm{agr}_K(g)=\mathrm{CA}_K(f,g)=K,\qquad \mathrm{agr}_K(f)\le\frac{(b+1)N}{2b^2}-1<T,
--   $$
--   and at least
--   $$
--   Z=\max\Bigl\{L-\Bigl\lfloor\frac{\delta\binom L2}{q-N}\Bigr\rfloor,\ \Bigl\lceil\frac{L(q-N)}{q-N+\delta(L-1)}\Bigr\rceil\Bigr\}\ \ge\ \frac12\min\Bigl\{L,\frac{q-N}{\delta}\Bigr\} \tag{5.1}
--   $$
--   distinct nonzero exceptional challenges at agreement $T$.
--
--   The theorem extends the quadratic-form construction beyond characteristic two: for fixed $b$ it gives decoding lists of size $N^{\Omega_b(\log N)}$ and quasipolynomial exceptional sets at rate $1/b^2$, with agreement approaching $1/b$.
--
--   **Formalization Note** No characteristic is assumed. $\mathbb F_b$ is any field with $b$ elements and an algebra map into $\mathbb B$; $D$ is an $\mathbb F_b$-submodule of $\mathbb B$ with $\dim D+h=2n$, $h\le1$ ($h=0$ forces $D=\mathbb B$). $K$, $T$ and $(b+1)N/(2b^2)-1$ are exact natural numbers; $L$, $\delta$, $Z$ are real numbers, with $\binom L2=L(L-1)/2$ and the Gaussian binomial `HScattered.Hyperplanes.gaussBinom`, encoded exactly as in the published Theorem 5.1. The pair lives on the image of $D$ in $\mathbb F$.
--
--   Differences from the source:
--   - encoding: B = F_{b^m}, F_b its subfield; D = B or an F_b-hyperplane in B, h = m − d ∈ {0, 1} → a finite field B with b^{2n} elements, a field Fb with b elements and Algebra Fb B, D : Submodule Fb B with finrank D + h = 2n and h ≤ 1; reason: the subfield of size b is unique, and dim D = 2n − h with h ∈ {0, 1} means D = B (h = 0) or a linear hyperplane (h = 1)
--   - reading: Z is given by (5.1) with these values of L, δ and q → Z defined by the max of (5.1), with the displayed inequality Z ≥ (1/2) min{L, (q − N)/δ} as a conclusion; reason: (5.1) displays both the formula and the inequality; the base mission's Theorem 5.1 states it the same way
--   - reading: there is a received pair … having at least Z distinct nonzero exceptional challenges … The pair can be chosen to satisfy agr_K(f) ≤ (b + 1)N/(2b²) − 1 < T → one pair (f, g) with all properties and one set S, 0 ∉ S, |S| ≥ Z, T ≤ agr_K(f + z g) for z ∈ S; reason: 'the pair can be chosen' keeps the other properties of the same pair; the set is the defining condition of Bad_T
--   - encoding: finite extension F ⊇ B → a finite field F with Algebra B F; the code over F lives on pushDomain F D; reason: an algebra map of fields is an embedding
-- source:
--   Dao, Kominers, Thaler, Zheng, Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields, STOC 2027 submission manuscript (2 November 2026, sha256 6c2d9ced…), Theorem 5.22 and eq. (5.1), p.50 (p.34 for (5.1))

import Mathlib
import Definitions.Def_HScattered_Hyperplanes_gaussBinom
import Definitions.Def_GoldProxGap_reedSolomon
import Definitions.Def_GoldProxGap_domainFinset

open Polynomial

open scoped Classical

namespace GoldProxGap.Supplement

/-- **Theorem 5.22 (Quadratic-form families on full fields and hyperplanes)**, p.50. Dao,
Kominers, Thaler, Zheng, *Counterexamples to Beyond-Johnson Proximity Gaps over Binary Fields*,
STOC 2027 submission manuscript (2 November 2026, sha256 6c2d9ced…).

"Let b be a prime power, m = 2n, and B = F_{b^m}. Let D = B or an F_b-hyperplane in B, and write
d = dim_{F_b} D, h = m − d ∈ {0, 1}, and N = b^d. Choose 2 ≤ t ≤ n − h, and put
K = N/b², T = N/b − (b − 1)N/b^{t+1}, L = b^{2t}·(b^t − 1)/(b − 1)·[n − h t]_{b²},
δ = (b − 1)N/b^{2t}.
Then there is a received word on D over B with at least L distinct codewords of C_K(D; B), each
agreeing with it on exactly T coordinates. For every finite extension F ⊇ B, with q = |F| > N,
there is a received pair satisfying agr_K(g) = CA_K(f, g) = K and having at least Z distinct
nonzero exceptional challenges at agreement T, where Z is given by (5.1) with these values of L,
δ, and q. The pair can be chosen to satisfy agr_K(f) ≤ (b + 1)N/(2b²) − 1 < T."

**Formalization Note.**
* No characteristic is assumed: `b` is any prime power, `B` any field with `b^{2n}` elements and
  `F_b` any field `Fb` with `b` elements and `Algebra Fb B` (its unique subfield of size `b`).
* `D` is an `F_b`-linear subspace `D : Submodule Fb B` with `dim D + h = 2n`, `h ∈ {0, 1}`:
  `h = 0` forces `D = B`, `h = 1` makes `D` a (linear) `F_b`-hyperplane. The domain is the finite
  set of its elements.
* `K`, `T` and `fBound = (b + 1)N/(2b²) − 1` are exact natural numbers (`d ≥ 2n − 1 ≥ 2t + 1`);
  `L`, `δ`, `Z` are real numbers, `[n − h t]_{b²} = gaussBinom (b²) (n − h) t`, and
  `Z = max{L − ⌊δ·L(L − 1)/2/(q − N)⌋, ⌈L(q − N)/(q − N + δ(L − 1))⌉}` is (5.1) with
  `(L choose 2) = L(L − 1)/2`, encoded exactly as in the published `GoldProxGap.theorem_5_1`;
  the inequality `Z ≥ (1/2) min{L, (q − N)/δ}` displayed in (5.1) is a conclusion.
* "Each agreeing with it on exactly T coordinates": at least `L` codewords `c` with
  `agreeCount w c = T`.
* `F ⊇ B` is every finite field with `Algebra B F` and `|F| > N`; the pair lives on the image
  `pushDomain F D`. "There is a received pair … The pair can be chosen to satisfy …" is one pair
  with all properties; "at least Z distinct nonzero exceptional challenges" is one set `S` of
  nonzero challenges with `T ≤ agr_K(f + z g)` for `z ∈ S` and `|S| ≥ Z`. -/
theorem theorem_5_22 (b : ℕ) (hb : IsPrimePow b) (n : ℕ) {B : Type} [Field B] [Fintype B]
    (hB : Fintype.card B = b ^ (2 * n)) (Fb : Type) [Field Fb] [Fintype Fb]
    (hFb : Fintype.card Fb = b) [Algebra Fb B] (h : ℕ) (hh : h ≤ 1) (D : Submodule Fb B)
    (hD : Module.finrank Fb D + h = 2 * n) (t : ℕ) (ht : 2 ≤ t) (htn : t ≤ n - h) :
    let d : ℕ := 2 * n - h
    let N : ℕ := b ^ d
    let K : ℕ := N / b ^ 2
    let T : ℕ := N / b - (b - 1) * N / b ^ (t + 1)
    let L : ℝ := (b : ℝ) ^ (2 * t) * (((b : ℝ) ^ t - 1) / ((b : ℝ) - 1)) *
      HScattered.Hyperplanes.gaussBinom ((b : ℝ) ^ 2) (n - h) t
    let δ : ℝ := ((b : ℝ) - 1) * (N : ℝ) / (b : ℝ) ^ (2 * t)
    let fBound : ℕ := (b + 1) * N / (2 * b ^ 2) - 1
    let Dom : Finset B := Finset.univ.filter (fun x => x ∈ D)
    (∃ w : Dom → B,
      L ≤ (((codewords Dom K).filter (fun c => agreeCount w c = T)).card : ℝ)) ∧
    ∀ (F : Type) [Field F] [Fintype F] [Algebra B F], N < Fintype.card F →
      let q : ℝ := Fintype.card F
      let DF : Finset F := pushDomain F Dom
      let Z : ℝ := max (L - (⌊δ * (L * (L - 1) / 2) / (q - N)⌋ : ℝ))
        (⌈L * (q - N) / (q - N + δ * (L - 1))⌉ : ℝ)
      (1 / 2 : ℝ) * min L ((q - N) / δ) ≤ Z ∧
      ∃ f g : DF → F,
        agr DF K g = K ∧ CA DF K f g = K ∧
        agr DF K f ≤ fBound ∧ fBound < T ∧
        ∃ S : Finset F, (0 : F) ∉ S ∧ Z ≤ (S.card : ℝ) ∧
          ∀ z ∈ S, T ≤ agr DF K (f + z • g) := by sorry

end GoldProxGap.Supplement
