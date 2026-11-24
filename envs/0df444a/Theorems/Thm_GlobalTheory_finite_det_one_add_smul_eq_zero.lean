-- Prove2me | Theorems.Thm_GlobalTheory_finite_det_one_add_smul_eq_zero
-- name    : GlobalTheory.finite_det_one_add_smul_eq_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:46:32.389935+00:00
-- url     : https://prove2.me/theorems/8841bc85-40b5-4fbd-91da-59f24a751ee9
-- title:
--   Global Theory: finite det one add smul eq zero
-- statement:
--   The Global Theory construction uses the finite det one add smul eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsNormOneCmFieldDetOneAddNeZero.lean#L21-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsNormOneCmFieldDetOneAddNeZero.lean#L21-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_ExistsNormOneCmFieldDetOneAddNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Matrix
open GlobalTheory

theorem GlobalTheory.finite_det_one_add_smul_eq_zero {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    {z : ℂ | det (1 + z • M) = 0}.Finite := by sorry
