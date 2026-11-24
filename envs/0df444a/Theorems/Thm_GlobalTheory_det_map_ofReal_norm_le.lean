-- Prove2me | Theorems.Thm_GlobalTheory_det_map_ofReal_norm_le
-- name    : GlobalTheory.det_map_ofReal_norm_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:15:25.672084+00:00
-- url     : https://prove2.me/theorems/2c9124d5-d53f-44b3-b9e2-8ad5ee1e3547
-- title:
--   Global Theory: det map of Real norm le
-- statement:
--   The Global Theory construction uses the det map of Real norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NormDetOfRealLeFactorialMulPow.lean#L38-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NormDetOfRealLeFactorialMulPow.lean#L38-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_NormDetOfRealLeFactorialMulPow
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

theorem GlobalTheory.det_map_ofReal_norm_le : ∀ (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (M : ℝ), 0 ≤ M → Y.PosSemidef →
    (M • (1 : Matrix (Fin g) (Fin g) ℝ) - Y).PosSemidef →
    ‖(Y.map Complex.ofReal).det‖ ≤ (g.factorial : ℝ) * M ^ g := by sorry
