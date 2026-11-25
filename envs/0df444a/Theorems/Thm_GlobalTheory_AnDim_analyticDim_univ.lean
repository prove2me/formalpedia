-- Prove2me | Theorems.Thm_GlobalTheory_AnDim_analyticDim_univ
-- name    : GlobalTheory.AnDim.analyticDim_univ
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:36:23.698646+00:00
-- url     : https://prove2.me/theorems/65c6d10f-5ffd-4c4b-85d6-49fbd196715c
-- title:
--   An Dim: analytic Dim univ
-- statement:
--   The An Dim construction uses the analytic Dim univ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/PointDimensionLtProjectiveLine.lean#L72-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/Divisors₂/PointDimensionLtProjectiveLine.lean#L72-L74

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

theorem GlobalTheory.AnDim.analyticDim_univ [Nonempty X] (A : FinHolAtlas d X) : analyticDim A Set.univ = d := by sorry
