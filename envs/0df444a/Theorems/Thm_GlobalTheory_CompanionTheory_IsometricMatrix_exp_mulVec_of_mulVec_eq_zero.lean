-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_IsometricMatrix_exp_mulVec_of_mulVec_eq_zero
-- name    : GlobalTheory.CompanionTheory.IsometricMatrix.exp_mulVec_of_mulVec_eq_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:48:30.661876+00:00
-- url     : https://prove2.me/theorems/ad984e11-87a6-4f4f-8904-158a88a49ea0
-- title:
--   Isometric Matrix: exp mul Vec of mul Vec eq zero
-- statement:
--   The Isometric Matrix construction uses the exp mul Vec of mul Vec eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/BlockBasisChangeEntries.lean#L7-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/BlockBasisChangeEntries.lean#L7-L18

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MatrixExpSmulMulEqMulExpSmulOfIntertwine
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_BlockBasisChangeEntries
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.IsometricMatrix

theorem GlobalTheory.CompanionTheory.IsometricMatrix.exp_mulVec_of_mulVec_eq_zero {m : ℕ} (N : Matrix (Fin m) (Fin m) ℂ) (x : Fin m → ℂ)
    (hx : N *ᵥ x = 0) : NormedSpace.exp N *ᵥ x = x := by sorry
