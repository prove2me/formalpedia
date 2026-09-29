-- Prove2me | Theorems.Thm_GaloisRep_mem_conditionLifts_residueField_of_isOfType
-- name    : GaloisRep.mem_conditionLifts_residueField_of_isOfType
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/ac49d928-4b54-5950-9074-5bbfcdf9f3b9
-- title:
--   Residual representation of type D lies in `conditionLifts`
-- statement:
--   Let $\mathcal{O}$ be a commutative local ring whose residue field $k =$ `IsLocalRing.ResidueField 𝒪` is finite, and let $\bar\rho$ be a residual Galois representation over $k$: a $k$-vector space $\bar\rho.V$ of rank $2$ together with a monoid homomorphism $\bar\rho.\rho$ from $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) = (\overline{\mathbb{Q}} \simeq_{\mathbb{Q}} \overline{\mathbb{Q}})$ to $\mathrm{End}_k(\bar\rho.V)$ factoring through a finite level. Let $\mathcal{D}$ be a predicate on rank-$2$ adically continuous Galois representations over local $\mathcal{O}$-algebras, and assume [`GaloisRep.IsDeformationCondition 𝒪 𝒟`](def/GaloisRep_DeformationCondition.html#L19), i.e. the five clauses that $\mathcal{D}$ is invariant under equivalence of representations, stable under base change along local $\mathcal{O}$-algebra maps, descends along injective base changes and along fibre-product diagrams (all over algebras satisfying `IsArtinianTestAlgebra`), and for noetherian adically complete residually trivial $\mathcal{O}$-algebras is equivalent to holding on all surjective quotients that are test algebras. Let $\rho_0$ be a continuous homomorphism from the Galois group to $\mathrm{GL}_2$ of the object [`Deformation.ProartinianCat.residueField`](def/Deformations_ProartinianCat.html#L188) (carrier $k$, discrete topology), let $b$ be a basis of $\bar\rho.V$ indexed by `Fin 2`, and suppose the matrix of $\rho_0(\sigma)$ equals the matrix of $\bar\rho.\rho(\sigma)$ in the basis $b$ for every $\sigma$; suppose also $\mathcal{D}$ holds of the adic representation $\bar\rho$ determines via [`GaloisRepAdic.ofResidualGaloisRep`](def/GaloisRep_Adic.html#L196). Then $\rho_0$ lies in [`GaloisRep.conditionLifts 𝒪 𝒟 ρ₀`](def/GaloisRep_ConditionLifts.html#L9) evaluated at `residueField`: it lies in the lift subfunctor of $\rho_0$ at that object, and for every Artinian pro-Artinian $\mathcal{O}$-algebra $B$, every morphism $f$ from `residueField` to $B$, every adic representation $\rho_B$ over $B$ and every $B$-basis of $\rho_B.V$ in which the matrices of $\rho_B$ agree with those of the pushforward of $\rho_0$ along $f$, the condition $\mathcal{D}(\rho_B)$ holds.
--
--   This is the non-emptiness input for the deformation problem cut out by a deformation condition $\mathcal{D}$: the residual representation itself, viewed at the residue field, satisfies the condition on every Artinian image. It is used by [`GaloisRep.nonempty_deformationRingData`](thm.html#GaloisRep.nonempty_deformationRingData) in the construction of the universal deformation ring of type $\mathcal{D}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_mem_conditionLifts_residueField_of_isOfType.lean

import Mathlib
import Definitions.Def_GaloisRep_DeformationCondition
import Definitions.Def_GaloisRep_ConditionLifts
import Definitions.Def_Deformations_ProartinianCompact

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits IsLocalRing Deformation Deformation.ProartinianCat

theorem GaloisRep.mem_conditionLifts_residueField_of_isOfType
    (𝒪 : Type) [CommRing 𝒪] [IsLocalRing 𝒪] [Finite (IsLocalRing.ResidueField 𝒪)]
    (ρbar : ResidualGaloisRep (IsLocalRing.ResidueField 𝒪))
    (𝒟 : ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop)
    (h𝒟 : GaloisRep.IsDeformationCondition 𝒪 𝒟)
    (ρ₀ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →ₜ* GL (Fin 2) (Deformation.ProartinianCat.residueField (𝓞 := 𝒪)))
    (b : Module.Basis (Fin 2) (IsLocalRing.ResidueField 𝒪) ρbar.V)
    (hρ₀ : ∀ σ, (ρ₀ σ).val = LinearMap.toMatrix b b (ρbar.ρ σ))
    (hbar : 𝒟 (GaloisRepAdic.ofResidualGaloisRep ρbar)) :
    ρ₀ ∈ GaloisRep.conditionLifts 𝒪 𝒟 ρ₀ Deformation.ProartinianCat.residueField := by sorry
