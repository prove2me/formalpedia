-- Prove2me | Theorems.Thm_GrothendieckLB_mehler_coefficients
-- name    : GrothendieckLB.mehler_coefficients
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:50:23.018707+00:00
-- url     : https://prove2.me/theorems/f794993c-9b0a-45e0-a6db-0249581acd82
-- title:
--   Section 7: Mehler's identity $H_{f,g}(t)=\frac\pi2\sum_m\langle P_mf,P_mg\rangle t^m$, so $b_1=\frac\pi2\langle P_1f,P_1g\rangle$, $b_3=\frac\pi2\langle P_3f,P_3g\rangle$
-- statement:
--   Let $f,g:\mathbb R^d\to\{\pm1\}$ be measurable, and let $H_{f,g}(t)=\frac\pi2\mathbb E[f(X)g(X_t')]$ be their correlation function, with $(X,X_t')$ standard Gaussian vectors with coordinatewise correlation $t$. Then Mehler's identity holds,
--   $$
--   H_{f,g}(t)=\frac\pi2\sum_{m\ge0}\langle P_mf,P_mg\rangle t^m\qquad(|t|<1),
--   $$
--   and in particular the Taylor coefficients of degree one and three at the origin are
--   $$
--   b_1=[t]H_{f,g}=\frac\pi2\langle P_1f,P_1g\rangle,\qquad b_3=[t^3]H_{f,g}=\frac\pi2\langle P_3f,P_3g\rangle .
--   $$
--   These formulas turn the affine inequality on $(b_1,b_3)$ into a statement about Hermite projections.
--
--   **Formalization Note** The published `GrothendieckConstant.coeff_hermite_moments` is the case of odd pairs of the two coefficient identities.
--
--   Differences from the source:
--   - generalization: odd sign functions (Part II introduction, p.30; p.43) → every measurable sign pair, oddness not assumed; reason: Definition 10.1 mixes sign pairs without oddness and the Section 7–8 argument never uses it; the odd case is a specialization
--   - encoding: P_m (m = 1, 3, and every m in the series) as orthogonal projections in L² → moment sums pmInner, p1Inner, p3Inner; reason: the moments are the coordinates of the projections in the orthonormal Hermite basis
--   - encoding: Mehler's series for the correlated pair (X, X′_t), t unrestricted on the page → HasSum for t ∈ (−1, 1); reason: the pair has a density only for |t| < 1, and t = ±1 are the degenerate pairs X′ = ±X outside the page's use
-- source:
--   Saha et al., New Lower and Upper Bounds for the Grothendieck Constant, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Section 7, p.31

import Mathlib
import Definitions.Def_GrothendieckLB_IsSignFn
import Definitions.Def_GrothendieckLB_pairCorr
import Definitions.Def_GrothendieckLB_taylorCoeff
import Definitions.Def_GrothendieckLB_pmInner
import Definitions.Def_GrothendieckLB_p1Inner
import Definitions.Def_GrothendieckLB_p3Inner

namespace GrothendieckLB

/-- Section 7, Mehler's identity and the coefficients it gives (Saha et al., *New Lower and Upper Bounds for the Grothendieck Constant*, arXiv:2608.11158 (held version, sha256 e7eb5d65…), Section 7, p.31): for every
measurable sign pair on `ℝ^d` and every `t ∈ (−1, 1)`,
`H_{f,g}(t) = (π/2) ∑_{m≥0} ⟨P_mf, P_mg⟩ tᵐ`, and
`b₁ = [t]H_{f,g} = (π/2)⟨P₁f, P₁g⟩`, `b₃ = [t³]H_{f,g} = (π/2)⟨P₃f, P₃g⟩`.

**Formalization Note** No oddness of `f, g` (the page says "signs"); the odd case of the two
coefficient identities is the published `GrothendieckConstant.coeff_hermite_moments`. The series is
stated on `|t| < 1`, where `(X, X′_t)` has a density. -/
theorem mehler_coefficients {d : ℕ} {f g : (Fin d → ℝ) → ℝ} (hf : IsSignFn f) (hg : IsSignFn g) :
    (∀ t ∈ Set.Ioo (-1 : ℝ) 1,
      HasSum (fun m : ℕ => (Real.pi / 2) * pmInner m f g * t ^ m) (pairCorr f g t)) ∧
    taylorCoeff 1 (pairCorr f g) = (Real.pi / 2) * p1Inner f g ∧
    taylorCoeff 3 (pairCorr f g) = (Real.pi / 2) * p3Inner f g := by sorry

end GrothendieckLB
