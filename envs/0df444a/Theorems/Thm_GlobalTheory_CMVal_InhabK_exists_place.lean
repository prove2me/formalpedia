-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_InhabK_exists_place
-- name    : GlobalTheory.CMVal.InhabK.exists_place
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:07:52.521135+00:00
-- url     : https://prove2.me/theorems/b8945eee-587a-408f-ab2d-d0a343e987d8
-- title:
--   Inhab K: exists place
-- statement:
--   The Inhab K construction uses the exists place property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsFinSetSplitPlacesCoprimeConductor.lean#L158-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsFinSetSplitPlacesCoprimeConductor.lean#L158-L164

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

theorem GlobalTheory.CMVal.InhabK.exists_place : ∃ v : HeightOneSpectrum (OF K), ((43 : ℕ) : OF K) ∈ v.asIdeal := by sorry
