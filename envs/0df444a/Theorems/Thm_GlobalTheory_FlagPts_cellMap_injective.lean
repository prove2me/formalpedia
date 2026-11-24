-- Prove2me | Theorems.Thm_GlobalTheory_FlagPts_cellMap_injective
-- name    : GlobalTheory.FlagPts.cellMap_injective
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:54:53.214412+00:00
-- url     : https://prove2.me/theorems/55b4e03e-bb25-40f2-8684-7a73b6986088
-- title:
--   Flag Pts: cell Map injective
-- statement:
--   The Flag Pts construction uses the cell Map injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/InjectiveCellMap.lean#L20-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/InjectiveCellMap.lean#L20-L68

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AutomorphicMembership_IsClosedFlagsIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_UniMatBlockTriangular
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InjectiveCellMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Module TopologicalSpace
open GlobalTheory GlobalTheory.FlagPts

theorem GlobalTheory.FlagPts.cellMap_injective (k : Type) [Field k] (ι : Type) [Fintype ι] (V : ι → Type) [∀ i, AddCommGroup (V i)]
    [∀ i, Module k (V i)] [∀ i, FiniteDimensional k (V i)] (b : Frames k V) :
    Function.Injective (cellMap b) := by sorry
