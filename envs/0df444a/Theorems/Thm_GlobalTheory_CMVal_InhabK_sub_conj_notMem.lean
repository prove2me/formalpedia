-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_InhabK_sub_conj_notMem
-- name    : GlobalTheory.CMVal.InhabK.sub_conj_notMem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:08:27.59782+00:00
-- url     : https://prove2.me/theorems/69204365-a69b-4e85-947c-aee0d19c6039
-- title:
--   Inhab K: sub conj not Mem
-- statement:
--   The Inhab K construction uses the sub conj not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsFinSetSplitPlacesCoprimeConductor.lean#L75-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IsFinSetSplitPlacesCoprimeConductor.lean#L75-L99

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
local notation "cj" => IsCMField.ringOfIntegersComplexConj E

theorem GlobalTheory.CMVal.InhabK.sub_conj_notMem {z : 𝓞 E} (hz : IsPrimitiveRoot z 21) {P : Ideal (𝓞 E)} (hP : P ≠ ⊤) : z - cj z ∉ P := by sorry
