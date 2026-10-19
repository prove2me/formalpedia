-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_EhrhardSmooth_qheat_concave
-- name    : OAI.GaussianPropeller.EhrhardSmooth.qheat_concave
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T06:11:19.222642+00:00
-- url     : https://prove2.me/theorems/7ea05227-6a49-4dc2-a882-6d9e1c7f4143
-- title:
--   Gaussian quantiles of heat flows preserve concavity
-- statement:
--   Let $E=\mathbb R^\iota$ be a finite-dimensional Euclidean space with standard Gaussian measure $\gamma$, and for a function $F$ on $E$ let $P_tF(x)=\int F(x+\sqrt t\,z)\,d\gamma(z)$ be the Gaussian heat semigroup. Let $\varphi$ and $\Phi$ be the standard normal density and distribution function, and $q=\Phi^{-1}$ on $(0,1)$. Let $f:E\to\mathbb R$ be concave and smooth, with gradient bounded by $L$ and continuous Hessian bounded by $D$. Then for every $T\ge0$ the function
--   $$
--   x\mapsto\Phi^{-1}\Bigl(P_T(\Phi\circ f)(x)\Bigr)
--   $$
--   is concave.
--
--   This smooth form of Ehrhard's inequality is later applied to soft minima of linear functions, which approximate cones.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/SmoothedConcavity.lean#L82-L143

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_OAI_Probability_GaussianPropeller_Deletion
import Definitions.Def_OAI_Probability_GaussianPropeller_Translation
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatConvolution
import Definitions.Def_OAI_Probability_GaussianPropeller_Quantile
import Definitions.Def_OAI_Probability_GaussianPropeller_QuantileCalculus
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatMaximum
import Definitions.Def_OAI_Probability_GaussianPropeller_SmoothedConcavity

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.EhrhardSmooth
universe uι
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
open Set Filter
open scoped Topology RealInnerProductSpace
open scoped NNReal
open GaussianPropeller.Quantile GaussianPropeller.HeatConvolution
variable {ι : Type uι} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "γ" => stdGaussian E

theorem OAI.GaussianPropeller.EhrhardSmooth.qheat_concave {f : E → ℝ} {g : E → E} {K : E → E →L[ℝ] E}
    (hf : ∀ x, HasFDerivAt f (innerSL ℝ (g x)) x)
    (hg : ∀ x, HasFDerivAt g (K x) x) (hK : Continuous K)
    {L : ℝ≥0} {D : ℝ} (hL : ∀ x, ‖g x‖ ≤ L) (hD : ∀ x, ‖K x‖ ≤ D)
    (hconc : ConcaveOn ℝ univ f) {T : ℝ} (hT : 0 ≤ T) :
    ConcaveOn ℝ univ (qheat f T) := by sorry
