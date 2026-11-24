-- Prove2me | Theorems.Thm_GlobalTheory_irreducible_algebraMap_adicCompletion_of_dvr
-- name    : GlobalTheory.irreducible_algebraMap_adicCompletion_of_dvr
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:56:13.442583+00:00
-- url     : https://prove2.me/theorems/4d497f83-c7dc-4f32-9670-74cb3ad07f0d
-- title:
--   Global Theory: irreducible algebra Map adic Completion of dvr
-- statement:
--   The Global Theory construction uses the irreducible algebra Map adic Completion of dvr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RangeAlgebraMapEqIInfDiscreteValuationSubring.lean#L501-L503
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/RangeAlgebraMapEqIInfDiscreteValuationSubring.lean#L501-L503

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_RangeAlgebraMapEqIInfDiscreteValuationSubring
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
variable (V : Type*) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
variable {V}

theorem GlobalTheory.irreducible_algebraMap_adicCompletion_of_dvr {π : V} (hπ : Irreducible π) :
    Irreducible (algebraMap V (AdicCompletion (maximalIdeal V) V) π) := by sorry
