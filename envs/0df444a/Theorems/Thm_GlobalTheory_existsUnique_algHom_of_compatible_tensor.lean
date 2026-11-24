-- Prove2me | Theorems.Thm_GlobalTheory_existsUnique_algHom_of_compatible_tensor
-- name    : GlobalTheory.existsUnique_algHom_of_compatible_tensor
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:39:44.848595+00:00
-- url     : https://prove2.me/theorems/96a529e8-fbae-42f9-8ff4-1dc00259de04
-- title:
--   Global Theory: exists Unique alg Hom of compatible tensor
-- statement:
--   The Global Theory construction uses the exists Unique alg Hom of compatible tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueAlgEquivOfCompatibleQuotient.lean#L153-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueAlgEquivOfCompatibleQuotient.lean#L153-L165

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsUniqueAlgEquivOfCompatibleQuotient
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open TensorProduct
variable {R : Type*} [CommRing R] (I : Ideal R)
variable [IsNoetherianRing R] [IsAdicComplete I R]
variable {A B : Type*} [Ring A] [Ring B] [Algebra R A] [Algebra R B]

theorem GlobalTheory.existsUnique_algHom_of_compatible_tensor [Module.Finite R B]
    (f : ∀ n : ℕ, (R ⧸ I ^ n) ⊗[R] A →ₐ[R ⧸ I ^ n] (R ⧸ I ^ n) ⊗[R] B)
    (hf : ∀ n x, adicTensorTransition I B n (f (n + 1) x) = f n (adicTensorTransition I A n x)) :
    ∃! g : A →ₐ[R] B, ∀ n a, (1 : R ⧸ I ^ n) ⊗ₜ[R] g a = f n (1 ⊗ₜ a) := by sorry
