-- Prove2me | Theorems.Thm_GlobalTheory_CMVal_IdeleModule_absNorm_pos
-- name    : GlobalTheory.CMVal.IdeleModule.absNorm_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:55:04.865392+00:00
-- url     : https://prove2.me/theorems/bbbd069f-42c5-49bc-912e-4d366a61b5c2
-- title:
--   Idele Module: abs Norm pos
-- statement:
--   The Idele Module construction uses the abs Norm pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ModFMulPosPrincipal.lean#L21-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ModFMulPosPrincipal.lean#L21-L24

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

theorem GlobalTheory.CMVal.IdeleModule.absNorm_pos (v : HeightOneSpectrum (𝓞 E)) : (0 : ℝ) < ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) := by sorry
