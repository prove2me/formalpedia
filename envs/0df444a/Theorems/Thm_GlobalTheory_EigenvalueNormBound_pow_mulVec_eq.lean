-- Prove2me | Theorems.Thm_GlobalTheory_EigenvalueNormBound_pow_mulVec_eq
-- name    : GlobalTheory.EigenvalueNormBound.pow_mulVec_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T13:03:33.85681+00:00
-- url     : https://prove2.me/theorems/dbc3ddcf-66c4-4825-a48b-6cf21be92f54
-- title:
--   Eigenvalue Norm Bound: pow mul Vec eq
-- statement:
--   The Eigenvalue Norm Bound construction uses the pow mul Vec eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/NormEigenvalueLeOne.lean#L5-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/NormEigenvalueLeOne.lean#L5-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_NormEigenvalueLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.EigenvalueNormBound

theorem GlobalTheory.EigenvalueNormBound.pow_mulVec_eq {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) (μ : ℂ)
    (h : Matrix.mulVec M v = μ • v) (k : ℕ) : Matrix.mulVec (M ^ k) v = μ ^ k • v := by sorry
