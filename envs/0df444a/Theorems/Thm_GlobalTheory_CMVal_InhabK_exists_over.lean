-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_InhabK_exists_over
-- name    : GlobalTheory.CMVal.InhabK.exists_over
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:07:41.255318+00:00
-- url     : https://prove2.me/theorems/5ed7b71f-7fd4-4879-92c4-4504252b77f2
-- title:
--   Inhab K: exists over
-- statement:
--   The Inhab K construction uses the exists over property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsFinSetSplitPlacesCoprimeConductor.lean#L31-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsFinSetSplitPlacesCoprimeConductor.lean#L31-L34

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
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.CMVal.InhabK.exists_over (v : HeightOneSpectrum (OF E)) : ∃ P : HeightOneSpectrum (𝓞 E), Over P v := by sorry
