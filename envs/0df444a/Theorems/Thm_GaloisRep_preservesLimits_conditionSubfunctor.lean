-- Prove2me | Theorems.Thm_GaloisRep_preservesLimits_conditionSubfunctor
-- name    : GaloisRep.preservesLimits_conditionSubfunctor
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/9b154df1-9bad-595c-82ac-c5f82059185d
-- title:
--   Limit preservation for the deformation-condition subfunctor
-- statement:
--   Let $\mathcal{O}$ be a local commutative ring, and let $\mathcal{D}$ assign to each local ring $A$ equipped with an $\mathcal{O}$-algebra structure a predicate on [`GaloisRepAdic A`](def/GaloisRep_Adic.html#L16), i.e. on rank-two free finite $A$-modules $V$ with a monoid homomorphism $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) \to \mathrm{End}_A(V)$ whose action is adically continuous (for each $n$ some finite subextension of $\mathbb{Q}$ acts trivially modulo $\mathfrak{m}_A^n$). Let $\rho_0$ be a continuous monoid homomorphism $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) \to \mathrm{GL}_2(k)$, where $k$ is the residue field of $\mathcal{O}$ with the discrete topology, viewed as a point of [`Deformation.repnFunctor (Fin 2) _ 𝒪`](def/Deformations_LiftFunctor.html#L18) at the object `ProartinianCat.residueField`. Assume $h_0$: $\rho_0$ itself lies in [`GaloisRep.conditionLifts 𝒪 𝒟 ρ₀`](def/GaloisRep_ConditionLifts.html#L9) at that object, i.e. $\rho_0$ reduces to $\rho_0$ and, for every Artinian object $B$ of the category of local pro-artinian topological $\mathcal{O}$-algebras with residue field $k$, every morphism $f$ from the residue field to $B$ and every [`GaloisRepAdic B`](def/GaloisRep_Adic.html#L16) admitting a basis indexed by $\mathrm{Fin}\ 2$ in which the Galois action is given by the matrices of $f \circ \rho_0$, the predicate $\mathcal{D}$ holds. Assume further that $k$ is finite and that $\mathcal{D}$ satisfies [`GaloisRep.IsDeformationCondition`](def/GaloisRep_DeformationCondition.html#L19) (invariance under isomorphism, stability under base change along local maps of Artinian test algebras, descent along injective base change and along fibre products, and the characterisation of $\mathcal{D}$ on noetherian adically complete algebras by its validity on all surjective Artinian quotients). Then the $\mathrm{Type}$-valued functor underlying [`GaloisRep.conditionSubfunctor 𝒪 𝒟 ρ₀`](def/GaloisRep_ConditionLifts.html#L22), sending $A$ to the set of continuous framed lifts of $\rho_0$ to $\mathrm{GL}_2(A)$ all of whose Artinian specialisations satisfy $\mathcal{D}$, preserves limits of all small shapes.
--
--   This is the continuity (limit-preservation) property of the framed deformation functor cut out by a deformation condition in Mazur's sense, which is what allows the functor to be handled by pro-representability arguments. It is used in the construction of the deformation ring data for such a condition, via [`GaloisRep.nonempty_deformationRingData`](thm.html#GaloisRep.nonempty_deformationRingData).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_preservesLimits_conditionSubfunctor.lean

import Mathlib
import Definitions.Def_GaloisRep_DeformationCondition
import Definitions.Def_GaloisRep_ConditionLifts
import Definitions.Def_Deformations_ConjQuotSubfunctor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory IsLocalRing

theorem GaloisRep.preservesLimits_conditionSubfunctor
    (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪]
    (𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop)
    (ρ₀ : (Deformation.repnFunctor (Fin 2) (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) 𝒪).obj
      Deformation.ProartinianCat.residueField)
    (h₀ : ρ₀ ∈ GaloisRep.conditionLifts 𝒪 𝒟 ρ₀ Deformation.ProartinianCat.residueField)
    [Finite (IsLocalRing.ResidueField 𝒪)]
    (h𝒟 : GaloisRep.IsDeformationCondition 𝒪 𝒟) :
    CategoryTheory.Limits.PreservesLimits (GaloisRep.conditionSubfunctor 𝒪 𝒟 ρ₀).toFunctor := by sorry
