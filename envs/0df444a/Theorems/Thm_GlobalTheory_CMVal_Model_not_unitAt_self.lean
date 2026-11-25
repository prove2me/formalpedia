-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Model_not_unitAt_self
-- name    : GlobalTheory.CMVal.Model.not_unitAt_self
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T11:59:16.776876+00:00
-- url     : https://prove2.me/theorems/c39b2c8d-e842-4327-92ca-5658ba1b610f
-- title:
--   Model: not unit At self
-- statement:
--   The Model construction uses the not unit At self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsValuedHeckeCharRamified.lean#L132-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsValuedHeckeCharRamified.lean#L132-L132

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

theorem GlobalTheory.CMVal.Model.not_unitAt_self {l : ℕ} (hl : l.Prime) : ¬ UnitAt l (l : ℂ) := by sorry
