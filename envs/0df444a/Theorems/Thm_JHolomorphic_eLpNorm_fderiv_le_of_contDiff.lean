-- Prove2me | Theorems.Thm_JHolomorphic_eLpNorm_fderiv_le_of_contDiff
-- name    : JHolomorphic.eLpNorm_fderiv_le_of_contDiff
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T17:30:04.412458+00:00
-- url     : https://prove2.me/theorems/50f85548-d3f1-471b-9462-64a23146d88d
-- title:
--   $L^p$ estimate for the Cauchy–Riemann operator $\partial_s + J_0\partial_t$ on $C^1_c(\mathbb{C}, E)$
-- statement:
--   Let $E$ be a finite-dimensional real normed space, let $J_0:E\to E$ be a real linear map with $J_0^2=-1$, and let $1<p<\infty$. There is a constant $C$ such that every $C^1$ map $g:\mathbb{C}\to E$ with compact support satisfies
--
--   $$\|\partial_s g\|_{L^p(\mathbb{C})}+\|\partial_t g\|_{L^p(\mathbb{C})}\le C\,\|\partial_s g+J_0\,\partial_t g\|_{L^p(\mathbb{C})},$$
--
--   where $z=s+it$ and $L^p$ is taken with respect to Lebesgue measure.
--
--   This is the $L^p$ estimate for the constant-coefficient Cauchy–Riemann operator $\partial_s+J_0\partial_t$ with values in an arbitrary finite-dimensional space carrying a complex structure. The constant depends only on $E$, $J_0$ and $p$.
--
--   **Formalization Note** $\partial_s g(z)$ is `fderiv ℝ g z 1` and $\partial_t g(z)$ is `fderiv ℝ g z Complex.I`. The exponent is the real number $p$, passed to `eLpNorm` as `ENNReal.ofReal p`; the constant $C$ is real and enters as `ENNReal.ofReal C`. No inner product or complex-vector-space structure on $E$ is assumed; $J_0$ is an `E →L[ℝ] E` with `J₀.comp J₀ = -id`.
-- source:
--   Standard (elliptic regularity for the Cauchy–Riemann operator; weak derivatives and mollifiers).

import Definitions.Def_JHolomorphic_Setting
import Theorems.Thm_DbarRegularity_cauchyRiemann_lp_complex
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

namespace JHolomorphic

open MeasureTheory

/-- For `1 < p < ∞` and a complex structure `J₀` on the finite-dimensional real space `E` there is
`C` such that every `C¹` map `g : ℂ → E` with compact support satisfies
`‖g_s‖_p + ‖g_t‖_p ≤ C ‖g_s + J₀ g_t‖_p`. -/
theorem eLpNorm_fderiv_le_of_contDiff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (p : ℝ) (hp : 1 < p) (J₀ : E →L[ℝ] E)
    (hJ₀ : J₀.comp J₀ = -ContinuousLinearMap.id ℝ E) :
    ∃ C : ℝ, ∀ g : ℂ → E, ContDiff ℝ 1 g → HasCompactSupport g →
      eLpNorm (fun z => fderiv ℝ g z 1) (ENNReal.ofReal p) volume +
          eLpNorm (fun z => fderiv ℝ g z Complex.I) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C *
          eLpNorm (fun z => fderiv ℝ g z 1 + J₀ (fderiv ℝ g z Complex.I)) (ENNReal.ofReal p)
            volume := by
  sorry

end JHolomorphic
