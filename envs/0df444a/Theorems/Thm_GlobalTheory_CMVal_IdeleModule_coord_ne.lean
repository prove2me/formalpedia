-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_IdeleModule_coord_ne
-- name    : GlobalTheory.CMVal.IdeleModule.coord_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:58:40.0571+00:00
-- url     : https://prove2.me/theorems/8d08b077-96bb-487d-9ad9-623d01e14e42
-- title:
--   Idele Module: coord ne
-- statement:
--   The Idele Module construction uses the coord ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ModFMulPosPrincipal.lean#L10-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ModFMulPosPrincipal.lean#L10-L12

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

theorem GlobalTheory.CMVal.IdeleModule.coord_ne (y : (Af E)ˣ) (v : HeightOneSpectrum (𝓞 E)) : Valued.v ((y : Af E) v) ≠ 0 := by sorry
