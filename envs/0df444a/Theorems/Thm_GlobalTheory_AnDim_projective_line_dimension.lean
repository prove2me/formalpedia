-- Prove2me | Theorems.Thm_GlobalTheory_AnDim_projective_line_dimension
-- name    : GlobalTheory.AnDim.projective_line_dimension
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:42:04.55222+00:00
-- url     : https://prove2.me/theorems/1175f35d-1030-5525-a0e6-838f8610eb25
-- title:
--   An Dim: projective line dimension
-- statement:
--   The An Dim construction uses the projective line dimension property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/PointDimensionLtProjectiveLine.lean#L232-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/PointDimensionLtProjectiveLine.lean#L232-L236

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsClosedOfIsAnalyticSubset
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__LogResolutionProjectiveLine_09840aae280abe50
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__PointDimensionLtProjectiveLine_f9cea2a23bf32842
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M GlobalTheory.IndefiniteRowSideFullHecke.BoundaryPolynomialFunctions GlobalTheory.LogResInt Filter Topology
noncomputable section
open GlobalTheory.AnDim
variable {d : ℕ} {X : Type} [TopologicalSpace X]

theorem GlobalTheory.AnDim.projective_line_dimension : IsIrreducibleAnalytic p1 Set.univ ∧ analyticDim p1 Set.univ = 1 ∧
    analyticDim p1 (singularLocus p1 Set.univ) < analyticDim p1 Set.univ := by sorry
