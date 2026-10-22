-- Prove2me | Theorems.Thm_JHolomorphic_exists_eLpNorm_fderiv_le_of_norm_sub_lt
-- name    : JHolomorphic.exists_eLpNorm_fderiv_le_of_norm_sub_lt
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-22T00:25:11.575885+00:00
-- url     : https://prove2.me/theorems/8cd9b1fb-7bbd-4c8a-aa63-6bd1f16d1154
-- title:
--   Stability of the planar $L^p$ estimate for $\partial_s+A\,\partial_t$ under perturbation of $A$
-- statement:
--   Let $E$ be a finite-dimensional real normed space, $p>1$, and $A:E\to E$ linear with $A^2=-1$. Then there are $\delta>0$ and $C\in\mathbb R$ such that for every linear $B:E\to E$ with $\|B-A\|<\delta$ and every compactly supported $C^1$ map $g:\mathbb C\to E$,
--   $$\|\partial_sg\|_{L^p}+\|\partial_tg\|_{L^p}\le C\,\|\partial_sg+B\,\partial_tg\|_{L^p}.$$
--   Here $z=s+it$, $\partial_sg=Dg(z)1$ and $\partial_tg=Dg(z)i$. The operator $B$ is not required to satisfy $B^2=-1$. This makes the planar Cauchy–Riemann type estimate locally uniform in the frozen structure.
--
--   **Formalization Note** `A : E →L[ℝ] E` with `A.comp A = -ContinuousLinearMap.id ℝ E`; `g` satisfies `ContDiff ℝ 1 g` and `HasCompactSupport g`; the norms are `eLpNorm (fun z => fderiv ℝ g z 1) (ENNReal.ofReal p) volume` etc., and the constant enters as `ENNReal.ofReal C`.
-- source:
--   Frozen-coefficient L^p estimates for the Cauchy-Riemann operator; used for C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Lecture 2, Theorem 2.22

import Definitions.Def_JHolomorphic_Setting
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Topology.Compactness.Compact

namespace JHolomorphic

open MeasureTheory Metric Filter Topology Set
open scoped ContDiff ENNReal NNReal

/-- Stability of the planar `L^p` estimate for `∂ₛ + A ∂ₜ` (`A² = -1`) under perturbation of
`A`: for `1 < p` there are `δ > 0` and `C` such that for every linear `B : E → E` with
`‖B - A‖ < δ` and every compactly supported `C¹` map `g : ℂ → E`,
`‖∂ₛg‖_p + ‖∂ₜg‖_p ≤ C ‖∂ₛg + B ∂ₜg‖_p`. -/
theorem exists_eLpNorm_fderiv_le_of_norm_sub_lt {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (p : ℝ) (hp : 1 < p) (A : E →L[ℝ] E)
    (hA : A.comp A = -ContinuousLinearMap.id ℝ E) :
    ∃ δ > 0, ∃ C : ℝ, ∀ B : E →L[ℝ] E, ‖B - A‖ < δ → ∀ g : ℂ → E, ContDiff ℝ 1 g →
      HasCompactSupport g →
      eLpNorm (fun z => fderiv ℝ g z 1) (ENNReal.ofReal p) volume +
          eLpNorm (fun z => fderiv ℝ g z Complex.I) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal C *
          eLpNorm (fun z => fderiv ℝ g z 1 + B (fderiv ℝ g z Complex.I)) (ENNReal.ofReal p)
            volume := by
  sorry

end JHolomorphic
