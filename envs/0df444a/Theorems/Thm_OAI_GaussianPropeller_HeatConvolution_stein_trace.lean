-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_HeatConvolution_stein_trace
-- name    : OAI.GaussianPropeller.HeatConvolution.stein_trace
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T06:04:26.865479+00:00
-- url     : https://prove2.me/theorems/fb3d4f1f-1990-49dc-9ccf-03ffbfe855d2
-- title:
--   Stein's identity for a vector field
-- statement:
--   Let $E=\mathbb R^\iota$ be a finite-dimensional Euclidean space with standard Gaussian measure $\gamma$, and for a function $F$ on $E$ let $P_tF(x)=\int F(x+\sqrt t\,z)\,d\gamma(z)$ be the Gaussian heat semigroup. Let $g:E\to E$ be bounded and differentiable with continuous bounded derivative $K$, and let $(e_i)$ be the standard orthonormal basis. Then for all $r\in\mathbb R$ and $x\in E$,
--   $$
--   \int\bigl\langle g(x+rz),z\bigr\rangle\,d\gamma(z)=r\int\sum_i\bigl\langle K(x+rz)\,e_i,e_i\bigr\rangle\,d\gamma(z).
--   $$
--
--   The right side is $r$ times the averaged divergence of $g$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/HeatConvolution.lean#L101-L157

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_OAI_Probability_GaussianPropeller_Deletion
import Definitions.Def_OAI_Probability_GaussianPropeller_Translation
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatConvolution

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.HeatConvolution
universe uV uι
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
variable {ι : Type uι} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "γ" => stdGaussian E

theorem OAI.GaussianPropeller.HeatConvolution.stein_trace {g : E → E} {K : E → E →L[ℝ] E}
    (hg : ∀ x, HasFDerivAt g (K x) x) (hcK : Continuous K)
    {C D : ℝ} (hC : ∀ x, ‖g x‖ ≤ C) (hD : ∀ x, ‖K x‖ ≤ D)
    (r : ℝ) (x : E) :
    (∫ z, ⟪g (x+r•z),z⟫ ∂γ) = r*(∫ z, ∑ i, ⟪K (x+r•z)
      (EuclideanSpace.basisFun ι ℝ i), EuclideanSpace.basisFun ι ℝ i⟫ ∂γ) := by sorry
