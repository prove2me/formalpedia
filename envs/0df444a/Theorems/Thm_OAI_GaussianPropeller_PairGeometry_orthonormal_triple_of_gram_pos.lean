-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_PairGeometry_orthonormal_triple_of_gram_pos
-- name    : OAI.GaussianPropeller.PairGeometry.orthonormal_triple_of_gram_pos
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T06:33:50.698606+00:00
-- url     : https://prove2.me/theorems/ebc947a6-2323-4433-a35b-b96096ed88a0
-- title:
--   Adapted orthonormal coordinates for two vectors
-- statement:
--   Let $e$ be a unit vector of a real inner product space and $u,v$ vectors orthogonal to $e$ that are linearly independent, $|u|^2|v|^2-\langle u,v\rangle^2>0$. Then there are orthonormal $f_0=e,f_1,f_2$ and reals $a,c>0$ and $b$ with
--   $$
--   u=af_1,\qquad v=bf_1+cf_2,\qquad (ac)^2=|u|^2|v|^2-\langle u,v\rangle^2 .
--   $$
--
--   These coordinates reduce three-dimensional Gaussian integrals over a cell to the triangle integral.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/PairBounds.lean#L39-L98

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
import Definitions.Def_OAI_Probability_GaussianPropeller_OneCell
import Definitions.Def_OAI_Probability_GaussianPropeller_Mills
import Definitions.Def_OAI_Probability_GaussianPropeller_Taylor
import Definitions.Def_OAI_Probability_GaussianPropeller_ProbabilityBounds
import Definitions.Def_OAI_Probability_GaussianPropeller_Attainment
import Definitions.Def_OAI_Probability_GaussianPropeller_PairIntegral

open OAI OAI.GaussianPropeller
universe uE
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
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology RealInnerProductSpace
open MeasureTheory Set Filter
open scoped Topology BigOperators
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology ENNReal
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem OAI.GaussianPropeller.PairGeometry.orthonormal_triple_of_gram_pos (e u v : E) (he : ‖e‖ = 1)
    (heu : ⟪e,u⟫ = 0) (hev : ⟪e,v⟫ = 0)
    (hd : 0 < ‖u‖^2*‖v‖^2-⟪u,v⟫^2) :
    ∃ (f : Fin 3 → E) (a b c : ℝ), Orthonormal ℝ f ∧
      f 0 = e ∧ 0 < a ∧ 0 < c ∧ u = a • f 1 ∧ v = b • f 1 + c • f 2 ∧
      (a*c)^2 = ‖u‖^2*‖v‖^2-⟪u,v⟫^2 := by sorry
