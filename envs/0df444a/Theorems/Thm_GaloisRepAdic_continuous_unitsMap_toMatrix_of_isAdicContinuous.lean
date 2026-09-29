-- Prove2me | Theorems.Thm_GaloisRepAdic_continuous_unitsMap_toMatrix_of_isAdicContinuous
-- name    : GaloisRepAdic.continuous_unitsMap_toMatrix_of_isAdicContinuous
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:46.235172+00:00
-- url     : https://prove2.me/theorems/cb066644-3d3e-5678-9388-0b7b7e64bbfe
-- title:
--   Adic continuity gives a continuous map to GL₂(A)
-- statement:
--   Let $\mathcal{O}$ be a commutative local ring and let $A$ be an object of [`Deformation.ProartinianCat`](def/Deformations_ProartinianCat.html#L44) $\mathcal{O}$, that is, a topological local $\mathcal{O}$-algebra which is pro-Artinian, whose structure map is local and which has the same residue field as $\mathcal{O}$; assume moreover [`IsLocalRing.IsAdicTopology A`](def/Patching_SystemTypes.html#L17), i.e. the topology of $A$ is the $\mathfrak{m}_A$-adic one. Let $\rho$ be a [`GaloisRepAdic A`](def/GaloisRep_Adic.html#L16): a finite free $A$-module $V$ with $\operatorname{rank}_A V = 2$ together with a monoid homomorphism $\rho.\rho$ from $\operatorname{Gal}(\overline{\mathbb{Q}}/\mathbb{Q}) = \operatorname{AlgebraicClosure}\mathbb{Q} \simeq_{\mathbb{Q}} \operatorname{AlgebraicClosure}\mathbb{Q}$ to $\operatorname{End}_A V$ satisfying [`GaloisActionIsAdicContinuous`](def/GaloisRep_Adic.html#L9): for every $n \in \mathbb{N}$ there is an intermediate field $L$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ with $L/\mathbb{Q}$ finite such that every $\sigma$ fixing $L$ pointwise satisfies $\rho(\sigma)v - v \in \mathfrak{m}_A^n \cdot V$ for all $v \in V$. Let $b$ be an $A$-basis of $V$ indexed by `Fin 2`. The assertion is that the map sending $\sigma$ to the image of the unit $\rho(\sigma)$ of $\operatorname{End}_A V$ under the unit-group functor applied to the algebra isomorphism $\operatorname{End}_A V \cong M_2(A)$ attached to $b$, viewed in $GL_2(A)$, is continuous for the Krull topology on the Galois group and the unit-group topology on $GL_2(A)$ coming from the $\mathfrak{m}_A$-adic topology on matrices.
--
--   This is the passage from an $\mathfrak{m}$-adic (algebraic) continuity condition on a rank-two Galois representation over a pro-Artinian coefficient ring to genuine topological continuity of the associated matrix representation, as in the formulation of deformation functors of Galois representations. It is used when matching representations over such coefficient rings with points of the representation/deformation functor, and is cited in the construction of deformation ring data and in the comparison of Hecke-algebra-valued representations with Galois representations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRepAdic_continuous_unitsMap_toMatrix_of_isAdicContinuous.lean

import Mathlib
import Definitions.Def_GaloisRep_Adic
import Definitions.Def_Deformations_ProartinianCat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem GaloisRepAdic.continuous_unitsMap_toMatrix_of_isAdicContinuous
    {𝒪 : Type} [CommRing 𝒪] [IsLocalRing 𝒪]
    (A : Deformation.ProartinianCat 𝒪) [IsLocalRing.IsAdicTopology A]
    (ρ : GaloisRepAdic A) (b : Module.Basis (Fin 2) A ρ.V) :
    Continuous (fun σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ =>
      (Units.map (LinearMap.toMatrixAlgEquiv b).toMonoidHom (ρ.ρ.toHomUnits σ) :
        GL (Fin 2) A)) := by sorry
