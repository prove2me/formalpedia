-- Prove2me | Theorems.Thm_GlobalTheory_finite_piece_of_polyGradedSMul
-- name    : GlobalTheory.finite_piece_of_polyGradedSMul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:49:51.11627+00:00
-- url     : https://prove2.me/theorems/2d8aa2c1-373a-406e-bbe9-1ed45b93a5d1
-- title:
--   Global Theory: finite piece of poly Graded SMul
-- statement:
--   The Global Theory construction uses the finite piece of poly Graded SMul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/FinitePieceOfPolyGradedSMul.lean#L9-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/FinitePieceOfPolyGradedSMul.lean#L9-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_ExistsAwayFracOfMemHomLoc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_XSmulMemWeightedHomogeneousSubmodule
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FinitePieceOfPolyGradedSMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits DirectSum MvPolynomial TensorProduct GlobalTheory
open GlobalTheory

theorem GlobalTheory.finite_piece_of_polyGradedSMul : ∀ (ι : Type) [LinearOrder ι] [Fintype ι] (R : Type)
    [CommRing R] (M : Type) [AddCommGroup M] [Module R M] [Module (MvPolynomial ι R) M]
    [IsScalarTower R (MvPolynomial ι R) M] (ℳ : ℤ → Submodule R M) [PolyGradedSMul ι ℳ]
    [Decomposition ℳ], Module.Finite (MvPolynomial ι R) M → ∀ n, Module.Finite R (ℳ n) := by sorry
