-- Prove2me | Theorems.Thm_IterRoundDet_lemma_3_4
-- name    : IterRoundDet.lemma_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T15:54:29.514013+00:00
-- url     : https://prove2.me/theorems/2404dfff-ffbe-451d-bfc0-849d3b512f7d
-- title:
--   Lemma 3.4 — the maximum-entropy dual of $f$
-- statement:
--   For every $(a,x)\in\mathcal R$,
--
--   $$f(a,x)=E_p(a)+\sum_i a_i\log x_i=\max_\mu\sum_S\mu(S)\log\frac{c_Sx^S}{\mu(S)},\qquad E_p(a)=\max_\mu\sum_S\mu(S)\log\frac{c_S}{\mu(S)},$$
--
--   where the maxima are over distributions $\mu$ on the sets $S$ with $c_S>0$ and $\mathbb E_\mu\mathbf 1_S=a$, and a term with $a_i=x_i=0$ is zero. This identity shows that $f$ is an entropy plus a linear term in $\log x$.
--
--   Differences from the source:
--   - encoding: a homogeneous multiaffine polynomial p of degree d → its coefficient function c with c S ≠ 0 → |S| = d; reason: footnote 2 is this form; the two are in bijection
--   - encoding: all coefficients have the same sign → non-negative coefficients inside IsStablePoly; reason: footnote 2 and §3.1 normalize to this; for a negative p the printed logarithms have no meaning
-- source:
--   Bansal, Li, Singh, Xu, Iterative Rounding for Determinant Maximization and Real Stable Polynomials, STOC 2027 submission (manuscript sha256 aa18bcee…), Lemma 3.4, p.14

import Mathlib
import Definitions.Def_IterRoundDet_StablePoly
import Definitions.Def_IterRoundDet_Polytopes
import Definitions.Def_IterRoundDet_Relaxation

set_option autoImplicit false

namespace IterRoundDet

/-- Bansal, Li, Singh, Xu, STOC 2027 submission (manuscript sha256 aa18bcee…), Lemma 3.4 (Maximum-entropy dual), p.14. For every `(a, x) ∈ R`,
`f(a, x) = E_p(a) + ∑_i a_i log x_i = max_μ ∑_S μ(S) log(c_S x^S / μ(S))`, `E_p(a) = max_μ ∑_S μ(S) log(c_S / μ(S))`,
where the maxima are over distributions `μ` on the sets `S` with `c_S > 0` and `E_μ 1_S = a`.

**Formalization Note.** `IsGreatest` says each maximum is attained, as "max" does. -/
theorem lemma_3_4 {n d : ℕ} {c : Finset (Fin n) → ℝ} (hc : IsStablePoly d c) {M : Matroid (Fin n)}
    (hM : M.E = Set.univ) {a x : Fin n → ℝ} (hax : Feasible c M a x) :
    relaxObj c a x = Ep c a + ∑ i, a i * Real.log (x i) ∧
    IsGreatest {t | ∃ μ, IsMarginalLaw c a μ ∧
      t = ∑ S, μ S * Real.log (c S * (∏ i ∈ S, x i) / μ S)} (relaxObj c a x) ∧
    IsGreatest {t | ∃ μ, IsMarginalLaw c a μ ∧ t = entropyVal c μ} (Ep c a) := by sorry

end IterRoundDet
