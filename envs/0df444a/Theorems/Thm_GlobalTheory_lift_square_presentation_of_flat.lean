-- Prove2me | Theorems.Thm_GlobalTheory_lift_square_presentation_of_flat
-- name    : GlobalTheory.lift_square_presentation_of_flat
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:07:31.616683+00:00
-- url     : https://prove2.me/theorems/517f5d13-8ce0-442b-95dc-f6f9d64c3220
-- title:
--   Global Theory: lift square presentation of flat
-- statement:
--   The Global Theory construction uses the lift square presentation of flat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LiftSquarePresentationOfFlat.lean#L8-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/LiftSquarePresentationOfFlat.lean#L8-L108

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_KerInfMapLeMapMulKerOfFlatTargetStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LeSupKerMulOfLeSupMaximalMulSectionStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LiftSquarePresentationOfFlat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
open GlobalTheory

theorem GlobalTheory.lift_square_presentation_of_flat : ∀ (O B A k H σ : Type) [CommRing O] [IsLocalRing O] [CommRing B] [CommRing A] [Algebra O B] [Algebra O A] [Algebra B A] [IsScalarTower O B A] [Module.Flat B A] [Field k] [CommRing H] [Algebra k H] [Fintype σ] (ε : A →ₐ[O] O) (π : O →+* k) (ρ : A →+* H) (εH : H →ₐ[k] k) (x : σ → A), Function.Surjective π → RingHom.ker π = IsLocalRing.maximalIdeal O → (∀ c : O, ρ (algebraMap O A c) = algebraMap k H (π c)) → (∀ a, εH (ρ a) = π (ε a)) → RingHom.ker ρ = (RingHom.ker (π.comp ((ε : A →+* O).comp (algebraMap B A)))).map (algebraMap B A) → Function.Surjective (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) → (RingHom.ker (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A)).FG → ∀ g : σ → MvPolynomial σ k, (∀ i, MvPolynomial.aeval (fun j => ρ (x j)) (g i) = 0) → RingHom.ker (MvPolynomial.aeval (fun j => ρ (x j)) : MvPolynomial σ k →ₐ[k] H) ≤ Ideal.span (Set.range g) ⊔ RingHom.ker (εH.comp (MvPolynomial.aeval (fun j => ρ (x j)) : MvPolynomial σ k →ₐ[k] H)) * RingHom.ker (MvPolynomial.aeval (fun j => ρ (x j)) : MvPolynomial σ k →ₐ[k] H) → ∃ f : σ → MvPolynomial σ B, (∀ i, MvPolynomial.aeval x (f i) = 0) ∧ RingHom.ker (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) ≤ Ideal.span (Set.range f) ⊔ (RingHom.ker ε).comap (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) * RingHom.ker (MvPolynomial.aeval x : MvPolynomial σ B →ₐ[B] A) := by sorry
