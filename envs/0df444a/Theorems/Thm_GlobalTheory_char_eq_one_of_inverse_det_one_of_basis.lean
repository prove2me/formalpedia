-- Prove2me | Theorems.Thm_GlobalTheory_char_eq_one_of_inverse_det_one_of_basis
-- name    : GlobalTheory.char_eq_one_of_inverse_det_one_of_basis
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:08:12.428064+00:00
-- url     : https://prove2.me/theorems/af8381b6-abc4-4dc4-85c8-84e6104da5c0
-- title:
--   Global Theory: char eq one of inverse det one of basis
-- statement:
--   The Global Theory construction uses the char eq one of inverse det one of basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DetCharacterReductionInvariant.lean#L10-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/DetCharacterReductionInvariant.lean#L10-L42

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_GeneralLinearGroupCharEqOneOfDetEqOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_DetCharacterReductionInvariant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open GlobalTheory
open scoped TensorProduct

theorem GlobalTheory.char_eq_one_of_inverse_det_one_of_basis {R S V Q A : Type} [CommRing R] [CommRing S] [Finite S] [Algebra R S]
    [AddCommGroup V] [Module R V] [Module S V] [IsScalarTower R S V] [AddCommGroup Q] [Module R Q] [CommGroup A]
    {r : ℕ} (b : Module.Basis (Fin r) S V) (e : Q ≃ₗ[R] V) (ψ : (Q ≃ₗ[R] Q) →* A)
    (h4 : ∀ 𝔪 : Ideal S, 𝔪.IsMaximal → 4 ≤ Nat.card (S ⧸ 𝔪)) (f : V →ₗ[S] V) (hf : LinearMap.det f = 1)
    (k : Q ≃ₗ[R] Q) (hk : ∀ q, f (e (k q)) = e q) : ψ k = 1 := by sorry
