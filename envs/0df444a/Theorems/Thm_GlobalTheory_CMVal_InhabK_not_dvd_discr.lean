-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_InhabK_not_dvd_discr
-- name    : GlobalTheory.CMVal.InhabK.not_dvd_discr
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:05:30.358387+00:00
-- url     : https://prove2.me/theorems/a678a221-ecd7-49fa-aac8-dfa57da25503
-- title:
--   Inhab K: not dvd discr
-- statement:
--   The Inhab K construction uses the not dvd discr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsFinSetSplitPlacesCoprimeConductor.lean#L144-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsFinSetSplitPlacesCoprimeConductor.lean#L144-L149

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousOfVal
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_UnramBridgeHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsFinSetSplitPlacesCoprimeConductor
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
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.InhabK

theorem GlobalTheory.CMVal.InhabK.not_dvd_discr : ¬ ((43 : ℕ) : ℤ) ∣ discr K := by sorry
