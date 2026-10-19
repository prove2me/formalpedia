-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_SmoothCDF_hess_bound
-- name    : OAI.GaussianPropeller.SmoothCDF.hess_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T06:08:37.208934+00:00
-- url     : https://prove2.me/theorems/fb5f225c-95c7-463a-b8f2-26902e022634
-- title:
--   Hessian bound for a Gaussian distribution function composed with a map
-- statement:
--   Let $\varphi$ and $\Phi$ be the standard normal density and distribution function, and $q=\Phi^{-1}$ on $(0,1)$. Let $f$ have gradient $g$ and Hessian $K$ with $|g|\le L$ and $\|K\|\le D$, where $L\ge0$. The Hessian of $\Phi\circ f$, namely $\varphi(f)K-f\varphi(f)\,g\otimes g$, satisfies at every point
--   $$
--   \bigl\|\nabla^2(\Phi\circ f)\bigr\|\le\varphi(0)\,\bigl(D+L^2\bigr).
--   $$
--
--   So smoothing $\Phi\circ f$ keeps uniform second-order control.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/QuantileCalculus.lean#L117-L133

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_OAI_Probability_GaussianPropeller_Deletion
import Definitions.Def_OAI_Probability_GaussianPropeller_Translation
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatConvolution
import Definitions.Def_OAI_Probability_GaussianPropeller_Quantile
import Definitions.Def_OAI_Probability_GaussianPropeller_QuantileCalculus

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.SmoothCDF
universe uE uι
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
open scoped RealInnerProductSpace
open GaussianPropeller.Quantile
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem OAI.GaussianPropeller.SmoothCDF.hess_bound {f : E → ℝ} {g : E → E} {K : E → E →L[ℝ] E} {L D : ℝ}
    (hL0 : 0 ≤ L) (hL : ∀ x, ‖g x‖ ≤ L) (hD : ∀ x, ‖K x‖ ≤ D) (x : E) :
    ‖hess f g K x‖ ≤ φ 0*(D+L^2) := by sorry
