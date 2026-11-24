-- Prove2me | Theorems.Thm_GlobalTheory_WpFam_Act_isRAct_gact
-- name    : GlobalTheory.WpFam.Act.isRAct_gact
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:56:24.366271+00:00
-- url     : https://prove2.me/theorems/1ba92486-e0b6-4d8b-8742-aaa1b31e764f
-- title:
--   Act: is RAct gact
-- statement:
--   The Act construction uses the is RAct gact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ModularGroupRowVecAndConjRightActions.lean#L34-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ModularGroupRowVecAndConjRightActions.lean#L34-L37

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

theorem GlobalTheory.WpFam.Act.isRAct_gact (N : ℕ) (D : GL (Fin 2) (ZMod N)) : IsRAct (gact N D) := by sorry
