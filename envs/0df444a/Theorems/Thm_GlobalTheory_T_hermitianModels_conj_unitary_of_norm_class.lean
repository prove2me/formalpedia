-- Prove2me | Theorems.Thm_GlobalTheory_T_hermitianModels_conj_unitary_of_norm_class
-- name    : GlobalTheory.T.hermitianModels_conj_unitary_of_norm_class
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:33:09.137834+00:00
-- url     : https://prove2.me/theorems/fc537af6-4591-4dbf-bbf5-6c44a03a9aea
-- title:
--   T: hermitian Models conj unitary of norm class
-- statement:
--   The T construction uses the hermitian Models conj unitary of norm class property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HermitianModelsConjUnitaryOfNormClassStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HermitianModelsConjUnitaryOfNormClassStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianModelsConjUnitaryOfNormClass
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_InertPlaceKappaOrbitalUnitEqSignedLatticeSumImpo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HermitianModelsConjUnitaryOfNormClassStatement
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

theorem GlobalTheory.T.hermitianModels_conj_unitary_of_norm_class : ∀ (K : GlobalTheory.UnitLemma.UQ) (B : GlobalTheory.UnitLemma.InvAlg K) (n : ℕ) (γ γ' : Matrix (Fin n) (Fin n) K.E) (x x' v : B.Aˣ) (ψ ψ' : B.A ≃ₗ[K.E] (Fin n → K.E)), GlobalTheory.InertUnitOrb.IsModel B γ x ψ → GlobalTheory.InertUnitOrb.IsModel B γ' x' ψ' → (x' : B.A) = x * (v * B.σ v) → ∃ u : Matrix (Fin n) (Fin n) K.E, (u.map K.c)ᵀ * u = 1 ∧ γ * u = u * γ' := by sorry
