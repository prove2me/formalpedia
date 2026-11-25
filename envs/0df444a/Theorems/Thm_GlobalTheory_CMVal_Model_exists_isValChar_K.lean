-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Model_exists_isValChar_K
-- name    : GlobalTheory.CMVal.Model.exists_isValChar_K
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:59:01.943986+00:00
-- url     : https://prove2.me/theorems/960443bd-fca6-41b0-8327-d48297f13e4c
-- title:
--   Model: exists is Val Char K
-- statement:
--   The Model construction uses the exists is Val Char K property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsValuedHeckeCharRamified.lean#L375-L382
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsValuedHeckeCharRamified.lean#L375-L382

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnramBridgeHolds
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExistsValuedHeckeCharRamified
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.Model

theorem GlobalTheory.CMVal.Model.exists_isValChar_K (s : ℕ) (κ : InfinitePlace K → ℕ) :
    ∃ v : HeightOneSpectrum (OF K), IsBaseCond (v.asIdeal ^ 2) ∧ IsFinSetSplitPlacesCoprimeConductor (v.asIdeal ^ 2) ∅ ∧ ∃ χ : HChar K,
      IsValChar (fun w : InfinitePlace K => w.embedding) s κ (v.asIdeal ^ 2) ∅ χ ∧ ∃ P, ¬ UnrAt χ P := by sorry
