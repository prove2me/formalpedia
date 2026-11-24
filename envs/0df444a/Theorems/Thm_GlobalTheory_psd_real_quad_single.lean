-- Prove2me | Theorems.Thm_GlobalTheory_psd_real_quad_single
-- name    : GlobalTheory.psd_real_quad_single
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:15:26.202859+00:00
-- url     : https://prove2.me/theorems/054b5b96-24e6-477a-92ec-b3a61f7afd90
-- title:
--   Global Theory: psd real quad single
-- statement:
--   The Global Theory construction uses the psd real quad single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NormDetOfRealLeFactorialMulPow.lean#L7-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/NormDetOfRealLeFactorialMulPow.lean#L7-L13

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

theorem GlobalTheory.psd_real_quad_single (g : ℕ) (Y : Matrix (Fin g) (Fin g) ℝ) (hY : Y.PosSemidef) (i j : Fin g)
    (hij : i ≠ j) (c : ℝ) : 0 ≤ Y i i + c * Y i j + c * Y j i + c * c * Y j j := by sorry
