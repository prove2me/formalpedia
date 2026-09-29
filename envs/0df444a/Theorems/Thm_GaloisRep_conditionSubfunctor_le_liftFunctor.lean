-- Prove2me | Theorems.Thm_GaloisRep_conditionSubfunctor_le_liftFunctor
-- name    : GaloisRep.conditionSubfunctor_le_liftFunctor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/e04542e9-d72d-5551-8615-4d74c1826fe9
-- title:
--   Condition subfunctor is contained in the framed lift functor
-- statement:
--   Let $\mathcal{O}$ be a commutative local ring, let $\mathcal{D}$ be a predicate assigning to each local $\mathcal{O}$-algebra $A$ a property of objects of [`GaloisRepAdic A`](def/GaloisRep_Adic.html#L16) (a finite free $A$-module $V$ of rank $2$ together with a monoid homomorphism from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) = \mathrm{AlgebraicClosure}\,\mathbb{Q} \simeq_{\mathbb{Q}} \mathrm{AlgebraicClosure}\,\mathbb{Q}$ to $\mathrm{End}_A V$ whose action is adically continuous), and let $\rho_0$ be an element of the value of [`Deformation.repnFunctor (Fin 2) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) 𝒪`](def/Deformations_LiftFunctor.html#L18) at the terminal object [`Deformation.ProartinianCat.residueField`](def/Deformations_ProartinianCat.html#L188), that is, a continuous monoid homomorphism from the absolute Galois group of $\mathbb{Q}$ to $GL_2$ of the residue field of $\mathcal{O}$, the latter carrying the discrete topology. The assertion is an inclusion of subfunctors of the functor sending a pro-Artinian local topological $\mathcal{O}$-algebra $A$ to the set of continuous homomorphisms $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) \to GL_2(A)$: the subfunctor [`GaloisRep.conditionSubfunctor 𝒪 𝒟 ρ₀`](def/GaloisRep_ConditionLifts.html#L22), whose value at $A$ consists of those $\rho'$ that reduce to $\rho_0$ along the unique map of $A$ to the residue field and for which $\mathcal{D}$ holds of every rank-two adically continuous Galois representation over an Artinian $B$ whose matrix in some basis is the pushforward of $\rho'$ along a morphism $A \to B$, is contained in [`Deformation.liftFunctor (Fin 2) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) 𝒪 ρ₀`](def/Deformations_LiftFunctor.html#L62), the subfunctor of framed lifts of $\rho_0$, whose value at $A$ is the preimage of $\{\rho_0\}$ under reduction to the residue field.
--
--   This records that imposing a deformation condition $\mathcal{D}$ cuts out a subfunctor of the functor of framed lifts of a fixed residual representation, in the sense of Mazur's and Ramakrishna's conditioned deformation functors. Together with the conjugation-stability, injective-reflection and limit-preservation properties of the same subfunctor it feeds the representability statements for conditioned deformation problems; it is used in [`GaloisRep.nonempty_deformationRingData`](thm.html#GaloisRep.nonempty_deformationRingData).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_conditionSubfunctor_le_liftFunctor.lean

import Mathlib
import Definitions.Def_GaloisRep_DeformationCondition
import Definitions.Def_GaloisRep_ConditionLifts
import Definitions.Def_Deformations_ConjQuotSubfunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory IsLocalRing

theorem GaloisRep.conditionSubfunctor_le_liftFunctor
    (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop)
    (ρ₀ : (Deformation.repnFunctor (Fin 2) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) 𝒪).obj
      Deformation.ProartinianCat.residueField) :
    GaloisRep.conditionSubfunctor 𝒪 𝒟 ρ₀ ≤
      Deformation.liftFunctor (Fin 2) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) 𝒪 ρ₀ := by sorry
