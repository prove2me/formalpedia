-- Prove2me | Theorems.Thm_GlobalTheory_existsUnique_bialgHom_of_compatible_tensor
-- name    : GlobalTheory.existsUnique_bialgHom_of_compatible_tensor
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:29:27.383358+00:00
-- url     : https://prove2.me/theorems/89403724-18ed-48cd-bde6-6b44ff7b5d03
-- title:
--   Global Theory: exists Unique bialg Hom of compatible tensor
-- statement:
--   The Global Theory construction uses the exists Unique bialg Hom of compatible tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueAlgEquivOfCompatibleQuotient.lean#L201-L223
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsUniqueAlgEquivOfCompatibleQuotient.lean#L201-L223

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
variable {A B : Type*} [Ring A] [Ring B] [Bialgebra R A] [Bialgebra R B]

theorem GlobalTheory.existsUnique_bialgHom_of_compatible_tensor [Module.Finite R B]
    (f : ∀ n : ℕ, (R ⧸ I ^ n) ⊗[R] A →ₐc[R ⧸ I ^ n] (R ⧸ I ^ n) ⊗[R] B)
    (hf : ∀ n x, adicTensorTransition I B n (f (n + 1) x) = f n (adicTensorTransition I A n x)) :
    ∃! g : A →ₐc[R] B, ∀ n a, (1 : R ⧸ I ^ n) ⊗ₜ[R] g a = f n (1 ⊗ₜ a) := by sorry
