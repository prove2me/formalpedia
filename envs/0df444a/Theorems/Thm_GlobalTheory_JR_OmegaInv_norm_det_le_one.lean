-- Prove2me | Theorems.Thm_GlobalTheory_JR_OmegaInv_norm_det_le_one
-- name    : GlobalTheory.JR.OmegaInv.norm_det_le_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T17:35:22.570667+00:00
-- url     : https://prove2.me/theorems/c20a0e3c-01f8-4d1d-92bc-5a6d1146376e
-- title:
--   Omega Inv: norm det le one
-- statement:
--   The Omega Inv construction uses the norm det le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisTransferFactorGlBorderedConjugation.lean#L10-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/JacquetRallisTransferFactorGlBorderedConjugation.lean#L10-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormMulApplyLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisTransferFactorKrylovDet
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_JacquetRallisTransferFactorGlBorderedConjugation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.OmegaInv

theorem GlobalTheory.JR.OmegaInv.norm_det_le_one {F : Type} [NormedField F] [IsUltrametricDist F] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) F) (hA : ∀ i j, ‖A i j‖ ≤ 1) : ‖A.det‖ ≤ 1 := by sorry
