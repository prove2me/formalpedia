-- Prove2me | Theorems.Thm_GlobalTheory_T_hermitian_adjoint_exists_unique_of_posDef
-- name    : GlobalTheory.T.hermitian_adjoint_exists_unique_of_posDef
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T10:13:52.376521+00:00
-- url     : https://prove2.me/theorems/279d4e63-3473-5fa1-8dd5-cd57cc553c85
-- title:
--   T: hermitian adjoint exists unique of pos Def
-- statement:
--   The T construction uses the hermitian adjoint exists unique of pos Def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/HermitianAdjointExistsUniqueOfPosDefStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/HermitianAdjointExistsUniqueOfPosDefStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HermitianAdjointExistsUniqueOfPosDef
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_HermitianAdjointExistsUniqueOfPosDefStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped ComplexConjugate
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.hermitian_adjoint_exists_unique_of_posDef : ∀ (A C : Type) [AddCommGroup A] [Module ℂ A] [AddCommGroup C] [Module ℂ C] [FiniteDimensional ℂ C] (ipA : A →ₗ[ℂ] A →ₗ⋆[ℂ] ℂ) (ip : C →ₗ[ℂ] C →ₗ⋆[ℂ] ℂ), (∀ x y, ip x y = conj (ip y x)) → (∀ x, x ≠ 0 → 0 < (ip x x).re) → ∀ (io : C →ₗ[ℂ] A) (u : A), ∃! x : C, ∀ y, ip y x = ipA (io y) u := by sorry
