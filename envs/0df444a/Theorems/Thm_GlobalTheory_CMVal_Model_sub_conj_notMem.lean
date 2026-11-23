-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_Model_sub_conj_notMem
-- name    : GlobalTheory.CMVal.Model.sub_conj_notMem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:59:28.029751+00:00
-- url     : https://prove2.me/theorems/fad7daa9-5f78-4f6c-bb18-6315330891e4
-- title:
--   Model: sub conj not Mem
-- statement:
--   The Model construction uses the sub conj not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsValuedHeckeCharRamified.lean#L255-L279
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Divisors/ExistsValuedHeckeCharRamified.lean#L255-L279

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
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
local notation "cj" => IsCMField.ringOfIntegersComplexConj E

theorem GlobalTheory.CMVal.Model.sub_conj_notMem {z : 𝓞 E} (hz : IsPrimitiveRoot z 21) {P : Ideal (𝓞 E)} (hP : P ≠ ⊤) : z - cj z ∉ P := by sorry
