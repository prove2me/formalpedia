-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_Pair_centroid_residual_pair
-- name    : OAI.GaussianPropeller.Pair.centroid_residual_pair
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T06:34:37.780093+00:00
-- url     : https://prove2.me/theorems/e2c45900-7c1b-49ec-984e-a10fee38e51e
-- title:
--   Residual pairs are bounded by the centroid of a cell
-- statement:
--   Let $\gamma$ be the standard Gaussian measure on a Euclidean space and $K$ a measurable set with centroid $z=\int_Kx\,d\gamma\ne0$. Let $r,s$ be orthogonal to $z$ and linearly independent, and $L,M>0$ with $\langle r,x\rangle\le L\langle z,x\rangle$ and $\langle s,x\rangle\le M\langle z,x\rangle$ on $K$. Then
--   $$
--   \sqrt{|r|^2|s|^2-\langle r,s\rangle^2}\le\frac{9\,|z|\,L\,M}{2\pi\sqrt{2\pi}} .
--   $$
--
--   The area spanned by the two residual directions is controlled by the length of the centroid.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/PairBounds.lean#L190-L249

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
open GaussianPropeller.PairIntegral
variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem OAI.GaussianPropeller.Pair.centroid_residual_pair (K : Set E) (hK : MeasurableSet K)
    (z r s : E) (hz : z ≠ 0) (hzK : ∫ x in K, x ∂stdGaussian E = z)
    (hzr : ⟪z,r⟫ = 0) (hzs : ⟪z,s⟫ = 0)
    {L M : ℝ} (hL : 0 < L) (hM : 0 < M)
    (hrK : ∀ x ∈ K, ⟪r,x⟫ ≤ L*⟪z,x⟫)
    (hsK : ∀ x ∈ K, ⟪s,x⟫ ≤ M*⟪z,x⟫)
    (hd : 0 < ‖r‖^2*‖s‖^2-⟪r,s⟫^2) :
    Real.sqrt (‖r‖^2*‖s‖^2-⟪r,s⟫^2) ≤
      9*‖z‖*L*M/(2*Real.pi*Real.sqrt (2*Real.pi)) := by sorry
