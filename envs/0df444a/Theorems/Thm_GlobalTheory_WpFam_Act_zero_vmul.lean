-- Prove2me | Theorems.Thm_GlobalTheory_WpFam_Act_zero_vmul
-- name    : GlobalTheory.WpFam.Act.zero_vmul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:43:09.867827+00:00
-- url     : https://prove2.me/theorems/720010c4-a6a9-4608-afd4-4012ec1dd3c7
-- title:
--   Act: zero vmul
-- statement:
--   The Act construction uses the zero vmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ModularGroupRowVecAndConjRightActions.lean#L31-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ModularGroupRowVecAndConjRightActions.lean#L31-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ModularGroupRowVecAndConjRightActions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam
open GlobalTheory GlobalTheory.WpFam GlobalTheory.WpFam.Act

theorem GlobalTheory.WpFam.Act.zero_vmul {N : ℕ} (α : GL (Fin 2) (ZMod N)) : vmul (0 : Fin 2 → ZMod N) α = 0 := by sorry
