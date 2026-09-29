-- Prove2me | Theorems.Thm_GaloisRep_moduleFinite_tangentSubmodule_of_tangentFinite
-- name    : GaloisRep.moduleFinite_tangentSubmodule_of_tangentFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/f79e716e-ec3e-5887-ba87-3f6c2ee87fc4
-- title:
--   Finiteness of the tangent space of a conditioned deformation ring
-- statement:
--   Let $\mathcal{O}$ be a local ring whose residue field $k=\mathrm{ResidueField}\,\mathcal{O}$ is finite, and let $\bar\rho$ be a residual Galois representation over $k$, i.e. a $k$-vector space of rank $2$ carrying a monoid homomorphism from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})=(\overline{\mathbb{Q}}\simeq_{\mathrm{alg}[\mathbb{Q}]}\overline{\mathbb{Q}})$ into its endomorphisms which factors through a finite level. Let $\mathcal{D}$ be a predicate on the rank-two adically continuous Galois representations [`GaloisRepAdic A`](def/GaloisRep_Adic.html#L16) over local $\mathcal{O}$-algebras $A$, assumed to be a deformation condition in the sense of [`GaloisRep.IsDeformationCondition`](def/GaloisRep_DeformationCondition.html#L19): stability under equivalence, under base change along local $\mathcal{O}$-algebra maps between Artinian test algebras, descent along injective such maps, gluing along surjective fibre products, and the characterisation of $\mathcal{D}$ on noetherian adically complete residue algebras by its validity on all surjective specialisations to Artinian test algebras. Let $\rho_0$ be a continuous homomorphism from the Galois group to $\mathrm{GL}_2$ of the pro-Artinian object with carrier $k$ and discrete topology, let $b$ be a basis of $\bar\rho$'s underlying space indexed by $\mathrm{Fin}\,2$, and assume each $\rho_0(\sigma)$ is the matrix of $\bar\rho(\sigma)$ in $b$, the associated matrix representation on $\mathrm{Fin}\,2\to k$ being absolutely irreducible (irreducible after base change to every field extension). Assume [`GaloisRep.TangentFinite`](def/GaloisRep_DeformationCondition.html#L59): the representations over the dual numbers $k[\varepsilon]$ satisfying $\mathcal{D}$ whose residual representation is equivalent to the base change of $\bar\rho$ to the residue field of $k[\varepsilon]$ form finitely many equivalence classes. Finally let $R$ be a pro-Artinian local $\mathcal{O}$-algebra corepresenting the functor sending an object $A$ to the image, in the conjugation quotient `repnQuotFunctor`, of the set `conditionLifts` of lifts of $\rho_0$ over $A$ of type $\mathcal{D}$. Then the $k$-module of tangent vectors of $R$ — those maps $R\to k$ which are additive, satisfy the Leibniz rule, vanish on the image of $\mathcal{O}$ and are locally constant — is a finite (finite-dimensional) $k$-module.
--
--   This is the finite-dimensionality of the tangent space $t_R\cong\mathrm{Hom}_{\mathcal{O}}(R,k[\varepsilon])$ of a deformation ring with deformation condition $\mathcal{D}$, deduced from the finiteness of the set of $\mathcal{D}$-deformations of $\bar\rho$ to the dual numbers. It feeds into [`GaloisRep.nonempty_deformationRingData`](thm.html#GaloisRep.nonempty_deformationRingData), where the data attached to the universal conditioned deformation ring are assembled.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_moduleFinite_tangentSubmodule_of_tangentFinite.lean

import Mathlib
import Definitions.Def_GaloisRep_DeformationCondition
import Definitions.Def_GaloisRep_ConditionLifts
import Definitions.Def_Deformations_ConjQuotSubfunctor
import Definitions.Def_Deformations_TangentSubmodule
import Definitions.Def_Representation_AbsolutelyIrreducible
import Definitions.Def_Deformations_MatrixRepresentation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory IsLocalRing

theorem GaloisRep.moduleFinite_tangentSubmodule_of_tangentFinite
    (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪] [Finite (ResidueField 𝒪)]
    (ρbar : ResidualGaloisRep (ResidueField 𝒪))
    (𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop)
    (h𝒟 : GaloisRep.IsDeformationCondition 𝒪 𝒟)
    (ρ₀ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →ₜ* GL (Fin 2) (Deformation.ProartinianCat.residueField (𝓞 := 𝒪)))
    (b : Module.Basis (Fin 2) (ResidueField 𝒪) ρbar.V)
    (hρ₀ : ∀ σ, (ρ₀ σ).val = LinearMap.toMatrix b b (ρbar.ρ σ))
    [Representation.IsAbsolutelyIrreducible.{0} (Deformation.matrixRepresentation ρ₀.toMonoidHom)]
    (hfin : GaloisRep.TangentFinite 𝒪 ρbar 𝒟)
    {R : Deformation.ProartinianCat 𝒪}
    (e : (Deformation.conjQuotSubfunctor (Fin 2) (GaloisRep.conditionSubfunctor 𝒪 𝒟 ρ₀)).toFunctor.CorepresentableBy R) :
    Module.Finite (IsLocalRing.ResidueField 𝒪) (Deformation.ProartinianCat.tangentSubmodule R) := by sorry
