-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_IdeleModule_modF_mul
-- name    : GlobalTheory.CMVal.IdeleModule.modF_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:07:20.67133+00:00
-- url     : https://prove2.me/theorems/0e1b0877-4bb0-4e04-88a2-d3e8c35bca69
-- title:
--   Idele Module: mod F mul
-- statement:
--   The Idele Module construction uses the mod F mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ModFMulPosPrincipal.lean#L26-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ModFMulPosPrincipal.lean#L26-L31

import Mathlib
import Definitions.Def_Formalism_PairingDivisors_StatementA
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IsFinSetSplitPlacesCoprimeConductor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ModFMulPosPrincipal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.CMVal
open GlobalTheory GlobalTheory.CMVal GlobalTheory.CMVal.IdeleModule
variable {E : Type} [Field E] [NumberField E]

theorem GlobalTheory.CMVal.IdeleModule.modF_mul (y y' : (Af E)ˣ) : modF (y * y') = modF y * modF y' := by sorry
