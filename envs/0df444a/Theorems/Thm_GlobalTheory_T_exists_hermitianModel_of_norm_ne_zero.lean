-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_hermitianModel_of_norm_ne_zero
-- name    : GlobalTheory.T.exists_hermitianModel_of_norm_ne_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:29:16.694186+00:00
-- url     : https://prove2.me/theorems/ef4bf03e-2ee5-59a8-aeb6-f03d1f10576d
-- title:
--   T: exists hermitian Model of norm ne zero
-- statement:
--   The T construction uses the exists hermitian Model of norm ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsHermitianModelOfNormNeZeroStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsHermitianModelOfNormNeZeroStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHermitianModelOfNormNeZero
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsHermitianModelOfNormNeZeroStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial Matrix
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_hermitianModel_of_norm_ne_zero : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (x : B.Aˣ), Module.finrank K.E B.A = n → B.σ (x : B.A) = x → B.N x ≠ 0 → ∃ (γ : Matrix (Fin n) (Fin n) K.E) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), GlobalTheory.InertUnitOrb.IsModel B γ x ψ := by sorry
