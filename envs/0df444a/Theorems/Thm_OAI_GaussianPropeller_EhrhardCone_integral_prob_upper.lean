-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_EhrhardCone_integral_prob_upper
-- name    : OAI.GaussianPropeller.EhrhardCone.integral_prob_upper
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T06:14:36.57611+00:00
-- url     : https://prove2.me/theorems/62137ec5-fc72-4d0f-b0d1-d3aae2b70bdd
-- title:
--   Integrated cone probabilities along a ray
-- statement:
--   Let $\gamma$ be the standard Gaussian measure on a Euclidean space $E$, and let $v_i$, $i\in\kappa$, be finitely many vectors with some $e$ satisfying $\langle v_i,e\rangle>0$ for all $i$. Let $C=\{y:\langle v_i,y\rangle\ge0\ \forall i\}$ and $p(x)=\gamma(\{y:x+y\in C\})$. Let $\varphi$ and $\Phi$ be the standard normal density and distribution function, and $q=\Phi^{-1}$. Let $h$ be a vector with $\beta=\langle h,\int_Cx\,d\gamma\rangle>0$, and put $a=\Phi^{-1}(p(0))$. Then
--   $$
--   \int_0^\infty p(-uh)\,du\le\frac{\varphi(a)\,\bigl(a\,p(0)+\varphi(a)\bigr)}{\beta}.
--   $$
--
--   Moving the cone along $h$ loses mass at least as fast as a half-space with the same mass and centroid pairing.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/ConeConcavity.lean#L306-L324

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
import Definitions.Def_OAI_Probability_GaussianPropeller_SoftMinimum
import Definitions.Def_OAI_Probability_GaussianPropeller_ConeConcavity

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.EhrhardCone
universe uX uι uκ
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
open Set Filter
open scoped Topology RealInnerProductSpace NNReal
open GaussianPropeller.Quantile
variable {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ] [Nonempty κ]
local notation "E" => EuclideanSpace ℝ ι
local notation "γ" => stdGaussian E

theorem OAI.GaussianPropeller.EhrhardCone.integral_prob_upper (v : κ → E) (e : E) (he : ∀ i, 0 < ⟪v i,e⟫)
    (h : E) (hβ : 0 < ⟪h, ∫ x in cone v, x ∂γ⟫) :
    (∫ u in Ioi (0:ℝ), prob v (-u • h)) ≤
      φ (q (prob v 0)) * (q (prob v 0)*prob v 0+φ (q (prob v 0))) /
      ⟪h, ∫ x in cone v, x ∂γ⟫ := by sorry
