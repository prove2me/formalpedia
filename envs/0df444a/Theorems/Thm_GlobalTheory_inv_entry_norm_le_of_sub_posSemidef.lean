-- Prove2me | Theorems.Thm_GlobalTheory_inv_entry_norm_le_of_sub_posSemidef
-- name    : GlobalTheory.inv_entry_norm_le_of_sub_posSemidef
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:56:03.972064+00:00
-- url     : https://prove2.me/theorems/78ebcfa1-10e5-4bc5-aef9-61e17d262fb2
-- title:
--   Global Theory: inv entry norm le of sub pos Semidef
-- statement:
--   The Global Theory construction uses the inv entry norm le of sub pos Semidef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/InvEntryNormLeOfSubSmulOnePosSemidef.lean#L7-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/InvEntryNormLeOfSubSmulOnePosSemidef.lean#L7-L66

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_InvEntryNormLeOfSubSmulOnePosSemidef
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
open GlobalTheory

theorem GlobalTheory.inv_entry_norm_le_of_sub_posSemidef (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (c : ℝ)
    (hc : 0 < c) (hY : (Y - c • (1 : Matrix (Fin g) (Fin g) ℝ)).PosSemidef) (i j : Fin g) :
    ‖(Y.map Complex.ofReal)⁻¹ i j‖ ≤ 1 / c := by sorry
