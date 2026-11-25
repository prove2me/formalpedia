-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_InhabK_expIn_eq_zero
-- name    : GlobalTheory.CMVal.InhabK.expIn_eq_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T11:58:06.694193+00:00
-- url     : https://prove2.me/theorems/fee8a38a-fc88-54b0-849a-889a5a4ceab4
-- title:
--   Inhab K: exp In eq zero
-- statement:
--   The Inhab K construction uses the exp In eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsFinSetSplitPlacesCoprimeConductor.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsFinSetSplitPlacesCoprimeConductor.lean#L25-L26

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

theorem GlobalTheory.CMVal.InhabK.expIn_eq_zero {𝔣 : Ideal (OF E)} {v : HeightOneSpectrum (OF E)} : expIn 𝔣 v = 0 ↔ ¬ v.asIdeal ∣ 𝔣 := by sorry
