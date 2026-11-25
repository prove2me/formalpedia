-- Prove2me | Theorems.Thm_GlobalTheory_T_hermitianModel_charpoly_eq_and_unitary
-- name    : GlobalTheory.T.hermitianModel_charpoly_eq_and_unitary
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:33:27.287333+00:00
-- url     : https://prove2.me/theorems/e17b26ef-fd2d-4ac0-8396-c5174f90c2d0
-- title:
--   T: hermitian Model charpoly eq and unitary
-- statement:
--   The T construction uses the hermitian Model charpoly eq and unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HermitianModelCharpolyEqAndUnitaryStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HermitianModelCharpolyEqAndUnitaryStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianModelCharpolyEqAndUnitary
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianModelCharpolyEqAndUnitaryStatement
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

theorem GlobalTheory.T.hermitianModel_charpoly_eq_and_unitary : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (γ : Matrix (Fin n) (Fin n) K.E) (x : B.Aˣ) (ψ : B.A ≃ₗ[K.E] (Fin n → K.E)), GlobalTheory.InertUnitOrb.IsModel B γ x ψ → γ.charpoly = B.P ∧ (B.g * B.σ B.g = 1 → (γ.map K.c)ᵀ * γ = 1) := by sorry
