-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_PolarisationModuleIndex_polMod_mul_le
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.polMod_mul_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:07:43.527122+00:00
-- url     : https://prove2.me/theorems/568a5e04-0f84-44ca-895d-acc65289f7a5
-- title:
--   Polarisation Module Index: pol Mod mul le
-- statement:
--   The Polarisation Module Index construction uses the pol Mod mul le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/PolarisationModuleIndex.lean#L104-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/PolarisationModuleIndex.lean#L104-L105

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_PolarisationModuleIndex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.CMVal
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex
variable {E : Type} [Field E] [NumberField E]
variable [IsCMField E]

theorem GlobalTheory.IndefiniteRowSideFullHecke.PolarisationModuleIndex.polMod_mul_le (L : Submodule (OF E) E) : polMod L * L ≤ dualLat L := by sorry
