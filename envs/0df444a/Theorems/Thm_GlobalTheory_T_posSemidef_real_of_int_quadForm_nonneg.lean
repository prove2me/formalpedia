-- Prove2me | Theorems.Thm_GlobalTheory_T_posSemidef_real_of_int_quadForm_nonneg
-- name    : GlobalTheory.T.posSemidef_real_of_int_quadForm_nonneg
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T12:36:07.767834+00:00
-- url     : https://prove2.me/theorems/570afc52-4de2-5c3a-b462-058e407b724d
-- title:
--   T: pos Semidef real of int quad Form nonneg
-- statement:
--   The T construction uses the pos Semidef real of int quad Form nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PosSemidefRealOfIntQuadFormNonnegStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/PosSemidefRealOfIntQuadFormNonnegStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PosSemidefRealOfIntQuadFormNonneg
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_PosSemidefRealOfIntQuadFormNonnegStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.posSemidef_real_of_int_quadForm_nonneg : ∀ (g : ℕ) (B : Matrix (Fin g) (Fin g) ℤ), B.IsSymm → (∀ v : Fin g → ℤ, 0 ≤ dotProduct v (B.mulVec v)) → (B.map (Int.cast : ℤ → ℝ)).PosSemidef := by sorry
