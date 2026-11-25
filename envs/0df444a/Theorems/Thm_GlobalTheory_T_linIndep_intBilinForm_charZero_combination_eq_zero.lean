-- Prove2me | Theorems.Thm_GlobalTheory_T_linIndep_intBilinForm_charZero_combination_eq_zero
-- name    : GlobalTheory.T.linIndep_intBilinForm_charZero_combination_eq_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:34:51.632808+00:00
-- url     : https://prove2.me/theorems/279863df-fb56-56e5-9141-72defc2c8ff9
-- title:
--   T: lin Indep int Bilin Form char Zero combination eq zero
-- statement:
--   The T construction uses the lin Indep int Bilin Form char Zero combination eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LinIndepIntBilinFormCharZeroCombinationEqZeroStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LinIndepIntBilinFormCharZeroCombinationEqZeroStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LinIndepIntBilinFormCharZeroCombinationEqZero
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LinIndepIntBilinFormCharZeroCombinationEqZeroStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.linIndep_intBilinForm_charZero_combination_eq_zero : ∀ {X : Type} [AddCommGroup X] {m : ℕ} (gam : Fin m → LinearMap.BilinForm ℤ X) (k : Type) [Field k] [CharZero k] (a : Fin m → k), LinearIndependent ℤ gam → (∀ y z, ∑ i, a i * (gam i y z : k) = 0) → a = 0 := by sorry
