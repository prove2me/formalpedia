-- Prove2me | Theorems.Thm_GlobalTheory_T_inv_entry_norm_le_of_sub_smul_one_posSemidef
-- name    : GlobalTheory.T.inv_entry_norm_le_of_sub_smul_one_posSemidef
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:33:46.478268+00:00
-- url     : https://prove2.me/theorems/83aee576-87ac-54ac-a543-f0a63d7deae3
-- title:
--   T: inv entry norm le of sub smul one pos Semidef
-- statement:
--   The T construction uses the inv entry norm le of sub smul one pos Semidef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/InvEntryNormLeOfSubSmulOnePosSemidefStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/InvEntryNormLeOfSubSmulOnePosSemidefStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InvEntryNormLeOfSubSmulOnePosSemidef
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InvEntryNormLeOfSubSmulOnePosSemidefStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.inv_entry_norm_le_of_sub_smul_one_posSemidef : ∀ (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (c : ℝ), 0 < c → (Y - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef → ∀ i j, ‖(Y.map Complex.ofReal)⁻¹ i j‖ ≤ 1 / c := by sorry
