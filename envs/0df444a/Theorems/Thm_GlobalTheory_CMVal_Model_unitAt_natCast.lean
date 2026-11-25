-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Model_unitAt_natCast
-- name    : GlobalTheory.CMVal.Model.unitAt_natCast
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T11:58:33.054671+00:00
-- url     : https://prove2.me/theorems/25adf28b-9279-5022-a51a-45f48b48b33b
-- title:
--   Model: unit At nat Cast
-- statement:
--   The Model construction uses the unit At nat Cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsValuedHeckeCharRamified.lean#L114-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsValuedHeckeCharRamified.lean#L114-L117

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

theorem GlobalTheory.CMVal.Model.unitAt_natCast {l m : ℕ} (hm : m ≠ 0) (h : m.Coprime l) : UnitAt l (m : ℂ) := by sorry
