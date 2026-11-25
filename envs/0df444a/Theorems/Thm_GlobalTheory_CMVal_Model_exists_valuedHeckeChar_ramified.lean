-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Model_exists_valuedHeckeChar_ramified
-- name    : GlobalTheory.CMVal.Model.exists_valuedHeckeChar_ramified
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:04:42.013829+00:00
-- url     : https://prove2.me/theorems/1a9c3acc-2877-4e4c-8c46-1790dd4fd50c
-- title:
--   Model: exists valued Hecke Char ramified
-- statement:
--   The Model construction uses the exists valued Hecke Char ramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsValuedHeckeCharRamified.lean#L414-L429
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsValuedHeckeCharRamified.lean#L414-L429

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

theorem GlobalTheory.CMVal.Model.exists_valuedHeckeChar_ramified (s : ℕ) (κ : InfinitePlace K → ℕ) :
    ∃ v q : HeightOneSpectrum (OF K), IsBaseCond (v.asIdeal ^ 2) ∧ IsFinSetSplitPlacesCoprimeConductor (v.asIdeal ^ 2) {q} ∧ ∃ χ : HChar K,
      IsValChar (fun w : InfinitePlace K => w.embedding) s κ (v.asIdeal ^ 2) {q} χ ∧ ∃ P, ¬ UnrAt χ P := by sorry
