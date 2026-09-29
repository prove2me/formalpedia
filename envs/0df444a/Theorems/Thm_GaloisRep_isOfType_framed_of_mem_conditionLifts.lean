-- Prove2me | Theorems.Thm_GaloisRep_isOfType_framed_of_mem_conditionLifts
-- name    : GaloisRep.isOfType_framed_of_mem_conditionLifts
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/b3593823-30e7-56db-9e9e-a329eb234a51
-- title:
--   Framed lifts in `conditionLifts` are of type D
-- statement:
--   Let $\mathcal{O}$ be a commutative local ring whose residue field is finite, and let $\mathcal{D}$ be a predicate assigning to every local $\mathcal{O}$-algebra $A$ a property of adically continuous rank-two Galois representations [`GaloisRepAdic A`](def/GaloisRep_Adic.html#L16) (a free $A$-module $V$ of rank $2$ together with a homomorphism from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ to $\mathrm{End}_A(V)^\times$ satisfying [`GaloisActionIsAdicContinuous`](def/GaloisRep_Adic.html#L9): for each $n$ there is a finite extension $L/\mathbb{Q}$ inside $\overline{\mathbb{Q}}$ such that every $\sigma$ fixing $L$ acts trivially on $V$ modulo $\mathfrak{m}_A^n V$). Assume [`GaloisRep.IsDeformationCondition 𝒪 𝒟`](def/GaloisRep_DeformationCondition.html#L19), i.e. the five clauses that $\mathcal{D}$ is invariant under equivalence of representations over Artinian test algebras, is preserved by base change along local $\mathcal{O}$-algebra maps of such algebras, descends along injective such base changes, descends along fibre products of test algebras, and, over a Noetherian local $\mathcal{O}$-algebra that is complete for its maximal ideal, with $\mathcal{O}$ mapping locally and onto the residue field, holds for $\rho$ exactly when it holds for all base changes of $\rho$ along surjective local $\mathcal{O}$-maps to Artinian test algebras. Let $\rho_0$ be a continuous homomorphism from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ to $\mathrm{GL}_2$ of the residue field of $\mathcal{O}$, regarded as an object of the pro-Artinian category $\mathcal{C}_{\mathcal{O}}$ with its discrete topology. Let $R$ be an object of $\mathcal{C}_{\mathcal{O}}$ (a topological local $\mathcal{O}$-algebra that is pro-Artinian, with $\mathcal{O}\to R$ local and inducing a surjection on residue fields) which is moreover Noetherian, $\mathfrak{m}_R$-adically complete, and whose topology is the $\mathfrak{m}_R$-adic one. Let $\rho^{u}$ be a continuous homomorphism from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ to $\mathrm{GL}_2(R)$ belonging to [`GaloisRep.conditionLifts 𝒪 𝒟 ρ₀ R`](def/GaloisRep_ConditionLifts.html#L9), that is: $\rho^{u}$ lies in the lift subfunctor of $\rho_0$, and for every Artinian object $B$ of $\mathcal{C}_{\mathcal{O}}$, every morphism $f : R \to B$, every $\rho_B \in$ [`GaloisRepAdic B`](def/GaloisRep_Adic.html#L16) and every basis $b$ of $\rho_B.V$ indexed by `Fin 2` for which the matrix of $\rho_B(\sigma)$ in $b$ is the pushforward of $\rho^{u}(\sigma)$ along $f$ for all $\sigma$, one has $\mathcal{D}(\rho_B)$. Finally assume that the action of $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ on $R^2$ obtained from $\rho^{u}$ by viewing a matrix as an endomorphism is adically continuous. The conclusion is that $\mathcal{D}$ holds of the representation in [`GaloisRepAdic R`](def/GaloisRep_Adic.html#L16) with module $R^2$, rank $2$, and Galois action given by $\rho^{u}$.
--
--   This is the non-trivial direction of the continuity clause of a deformation condition in Mazur's sense: being of type $\mathcal{D}$ over a complete Noetherian local ring is detected on Artinian quotients, so a framed lift all of whose Artinian specialisations are of type $\mathcal{D}$ is itself of type $\mathcal{D}$. It supplies the 'of type $\mathcal{D}$' datum for the universal framed deformation over the deformation ring, and is used by [`GaloisRep.nonempty_deformationRingData`](thm.html#GaloisRep.nonempty_deformationRingData); the finiteness of the residue field of $\mathcal{O}$ enters through [`IsProartinian.finite_quotient_of_isOpen`](thm.html#IsProartinian.finite_quotient_of_isOpen), which makes the quotients of $R$ by open ideals Artinian test algebras.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_isOfType_framed_of_mem_conditionLifts.lean

import Mathlib
import Definitions.Def_GaloisRep_DeformationCondition
import Definitions.Def_GaloisRep_ConditionLifts
import Definitions.Def_Deformations_ProartinianCompact

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits IsLocalRing Deformation Deformation.ProartinianCat

theorem GaloisRep.isOfType_framed_of_mem_conditionLifts
    (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    (𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop)
    (h𝒟 : GaloisRep.IsDeformationCondition 𝒪 𝒟)
    (ρ₀ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →ₜ* GL (Fin 2) (Deformation.ProartinianCat.residueField (𝓞 := 𝒪)))
    {R : Deformation.ProartinianCat 𝒪} [IsNoetherianRing R] [IsAdicComplete (IsLocalRing.maximalIdeal R) R]
    [IsLocalRing.IsAdicTopology R]
    (ρu : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →ₜ* GL (Fin 2) R)
    (hρu : ρu ∈ GaloisRep.conditionLifts 𝒪 𝒟 ρ₀ R)
    (hcont : GaloisActionIsAdicContinuous R
      ((Units.coeHom _).comp (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp ρu.toMonoidHom))) :
    𝒟 ({ V := Fin 2 → R, finrank_eq := by simp,
          ρ := (Units.coeHom _).comp (Matrix.GeneralLinearGroup.toLin.toMonoidHom.comp ρu.toMonoidHom),
          isAdicContinuous := hcont } : GaloisRepAdic R) := by sorry
