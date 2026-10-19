-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_EhrhardCone_prob_mem
-- name    : OAI.GaussianPropeller.EhrhardCone.prob_mem
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T06:13:57.648922+00:00
-- url     : https://prove2.me/theorems/cebb4ac5-2c1a-4bfe-b211-7b9c3fd98742
-- title:
--   Shifted cones have Gaussian probability strictly between 0 and 1
-- statement:
--   Let $\gamma$ be the standard Gaussian measure on a Euclidean space $E$, and let $v_i$, $i\in\kappa$, be finitely many vectors with some $e$ satisfying $\langle v_i,e\rangle>0$ for all $i$. Let $C=\{y:\langle v_i,y\rangle\ge0\ \forall i\}$ and $p(x)=\gamma(\{y:x+y\in C\})$. Then for every $x\in E$,
--   $$
--   0<p(x)<1 .
--   $$
--
--   So the Gaussian quantile $\Phi^{-1}(p(x))$ is a finite real number.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/ConeConcavity.lean#L50-L76

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
open GaussianPropeller.Quantile GaussianPropeller.EhrhardSmooth
variable {ι : Type uι} {κ : Type uκ} [Fintype ι] [Fintype κ] [Nonempty κ]
local notation "E" => EuclideanSpace ℝ ι
local notation "γ" => stdGaussian E

theorem OAI.GaussianPropeller.EhrhardCone.prob_mem (v : κ → E) (e : E) (he : ∀ i, 0 < ⟪v i,e⟫) (x : E) :
    prob v x ∈ Ioo (0:ℝ) 1 := by sorry
