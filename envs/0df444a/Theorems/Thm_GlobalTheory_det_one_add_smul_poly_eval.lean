-- Prove2me | Theorems.Thm_GlobalTheory_det_one_add_smul_poly_eval
-- name    : GlobalTheory.det_one_add_smul_poly_eval
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:53:52.990811+00:00
-- url     : https://prove2.me/theorems/62a7efc4-dcf3-455f-a7f0-887870f49d53
-- title:
--   Global Theory: det one add smul poly eval
-- statement:
--   The Global Theory construction uses the det one add smul poly eval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsNormOneCmFieldDetOneAddNeZero.lean#L6-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/ExistsNormOneCmFieldDetOneAddNeZero.lean#L6-L12

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

theorem GlobalTheory.det_one_add_smul_poly_eval {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (z : ℂ) :
    Polynomial.eval z (det (1 + (Polynomial.X : Polynomial ℂ) • M.map Polynomial.C)) = det (1 + z • M) := by sorry
