-- Prove2me | Theorems.Thm_GrothendieckPD_Digits_lemma_3_3
-- name    : GrothendieckPD.Digits.lemma_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:07:00.738089+00:00
-- url     : https://prove2.me/theorems/791e7386-13b5-47c8-b0db-212720611512
-- title:
--   Lemma 3.3: $\mathcal K=\overline{\mathcal C}$ in $\ell_1$
-- statement:
--   Let $\mathcal K\subseteq\ell_1$ be the set of coefficient sequences $c(\mu)$ for distributions $\mu$ on pairs of odd $f,g\in L^2(X)$ on the graded Gaussian space with $f(X),g(X)\in\{\pm1\}$ almost surely. Then
--   $$\mathcal K=\overline{\mathcal C},$$
--   the closure of the set $\mathcal C$ of Theorem 2.2 (finite-dimensional odd schemes) in $\ell_1$. The formal statement also asserts $\mathcal K\subseteq\ell_1$.
--
--   The lemma shows that passing to the graded space adds only limit points, so a rounding scheme on the graded space certifies the same kind of bound as a finite-dimensional one.
--
--   Differences from the source:
--   - encoding: variables X_i^{(d)}, grade d ≥ 1, i = 1, 2, … → coordinates of ℕ+ × ℕ → ℝ under the product of standard Gaussians; X_i^{(d)} is coordinate (d, i), the index i = 0 being an extra unused variable of each grade; reason: countably many i.i.d. N(0,1) variables of each grade, as on pp. 7–8
--   - reading: a distribution µ on pairs of functions → jointly measurable random pairs: GradedScheme for 𝒦 and GrothendieckLB.MixedScheme for 𝒞; reason: the source specifies no σ-algebra on function pairs; these realize distributions of L² classes by jointly measurable representatives, including all finite mixtures
--   - encoding: K = C̄ for subsets of ℓ1 → {c ∈ ℓ1 : c ∈ 𝒦} = closure {c ∈ ℓ1 : c ∈ 𝒞} in lp 1, together with 𝒦 ⊆ ℓ1; reason: the source states 𝒦 ⊆ ℓ1 in the hypothesis-free definition; 𝒞 ⊆ ℓ1 by Lemma 2.5, so nothing is lost
--   - encoding: odd f ∈ L²(X) with f(X) ∈ {±1} → f ∈ L², f ∈ {±1} a.s., f(X̃) = −f(X) a.s.; reason: the definitions of §3.1–3.2
-- source:
--   Steven Heilman, Chris Jones, Giulio Malavolta, Primal/Dual Method for the Grothendieck Constant, STOC 2027 submission #820 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/820.pdf, Lemma 3.3, p. 8

import Mathlib
import Definitions.Def_GrothendieckPD_Digits_GradedSpace

namespace GrothendieckPD.Digits

/-- Lemma 3.3 (p. 8). `𝒦 ⊆ ℓ1`, and `𝒦` equals the closure of `𝒞` in `ℓ1`, where `𝒦` is the set of
`c(µ)` for distributions `µ` on pairs of odd asymptotic Boolean functions on the graded space and
`𝒞` the set of Theorem 2.2. -/
theorem lemma_3_3 :
    (∀ c ∈ KSet, Memℓp c 1) ∧
      {c : lp (fun _ : ℕ => ℝ) 1 | ⇑c ∈ KSet} =
        closure {c : lp (fun _ : ℕ => ℝ) 1 | ⇑c ∈ CSet} := by sorry

end GrothendieckPD.Digits
