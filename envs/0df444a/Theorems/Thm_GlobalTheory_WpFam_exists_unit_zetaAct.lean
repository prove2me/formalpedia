-- Prove2me | Theorems.Thm_GlobalTheory_WpFam_exists_unit_zetaAct
-- name    : GlobalTheory.WpFam.exists_unit_zetaAct
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:43:11.868264+00:00
-- url     : https://prove2.me/theorems/6de4b3c8-d37d-45eb-9289-01d4e6585ea2
-- title:
--   Wp Fam: exists unit zeta Act
-- statement:
--   The Wp Fam construction uses the exists unit zeta Act property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnitZetaAct.lean#L13-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsUnitZetaAct.lean#L13-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ZetaActRefl
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsUnitZetaAct
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
open GlobalTheory GlobalTheory.WpFam

theorem GlobalTheory.WpFam.exists_unit_zetaAct : ∀ (N : ℕ) [NeZero N] (g : ℂ ≃+* ℂ), ∃ a : (ZMod N)ˣ, ZetaAct g N a := by sorry
