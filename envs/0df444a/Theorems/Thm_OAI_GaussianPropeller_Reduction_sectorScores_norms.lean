-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_Reduction_sectorScores_norms
-- name    : OAI.GaussianPropeller.Reduction.sectorScores_norms
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T06:27:45.308357+00:00
-- url     : https://prove2.me/theorems/e65b2c58-f63b-4fd8-a521-963bff54920d
-- title:
--   Norms of the propeller score vectors
-- statement:
--   For $d\ge2$ let $e_0,e_1$ be the first two coordinate vectors of $\mathbb R^d$ and let the propeller score tuple be $\bigl(2\sqrt3e_0,\ -\sqrt3e_0+3e_1,\ -\sqrt3e_0-3e_1\bigr)$. Then the tuple has squared norm $36$, and all pairwise distances equal $6$:
--   $$
--   |v_0-v_1|=|v_0-v_2|=|v_1-v_2|=6 .
--   $$
--
--   The three vectors form an equilateral triangle centred at the origin.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/Attainment.lean#L228-L256

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

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.Reduction
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
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

theorem OAI.GaussianPropeller.Reduction.sectorScores_norms (d : ℕ) (hd : 2 ≤ d) :
    ‖sectorScores d hd‖^2 = 36 ∧
    ‖(sectorScores d hd).ofLp 0 - (sectorScores d hd).ofLp 1‖ = 6 ∧
    ‖(sectorScores d hd).ofLp 0 - (sectorScores d hd).ofLp 2‖ = 6 ∧
    ‖(sectorScores d hd).ofLp 1 - (sectorScores d hd).ofLp 2‖ = 6 := by sorry
