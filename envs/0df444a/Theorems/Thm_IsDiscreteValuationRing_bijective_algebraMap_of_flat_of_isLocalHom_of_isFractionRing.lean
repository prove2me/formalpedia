-- Prove2me | Theorems.Thm_IsDiscreteValuationRing_bijective_algebraMap_of_flat_of_isLocalHom_of_isFractionRing
-- name    : IsDiscreteValuationRing.bijective_algebraMap_of_flat_of_isLocalHom_of_isFractionRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/b55ea2e2-96f8-59b1-a30f-1ebdc712d26f
-- title:
--   Flat birational local extension of a DVR is an equality
-- statement:
--   Let $O'$ be a commutative noetherian local ring, let $O$ be a commutative domain which is a discrete valuation ring, and let $F$ be a field, with algebra maps $O' \to O$, $O \to F$, $O' \to F$ forming a scalar tower (so $O' \to O$ followed by $O \to F$ is the map $O' \to F$), and with $F$ a fraction field of $O$ and also a fraction field of $O'$; thus the extension is birational. Assume the structure map $\operatorname{algebraMap} : O' \to O$ is a local homomorphism (preimage of the maximal ideal is the maximal ideal, in the `IsLocalHom` sense), that $O$ is flat as an $O'$-module, and that $\operatorname{algebraMap} : O' \to O$ is injective. Assume finally that there is an element $\pi \in O'$ with $\pi \neq 0$ such that the principal ideal $(\pi)$ is prime. The conclusion is that $\operatorname{algebraMap} : O' \to O$ is bijective, i.e. $O' \to O$ is an isomorphism of rings, $O' = O$.
--
--   This is the domination criterion used in the construction of Néron models (Bosch–Lütkebohmert–Raynaud 4.3): a flat birational local extension of a noetherian local ring with a nonzero principal prime by a discrete valuation ring is an equality. It is applied in [`AlgebraicGeometry.exists_isOpenImmersion_of_formallySmooth_stalk_of_isFractionRing_of_isDiscreteValuationRing`](thm.html#AlgebraicGeometry.exists_isOpenImmersion_of_formallySmooth_stalk_of_isFractionRing_of_isDiscreteValuationRing) to identify a local ring of a scheme with the local ring of a model over a discrete valuation ring.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDiscreteValuationRing_bijective_algebraMap_of_flat_of_isLocalHom_of_isFractionRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem IsDiscreteValuationRing.bijective_algebraMap_of_flat_of_isLocalHom_of_isFractionRing
    {O' O F : Type*} [CommRing O'] [IsNoetherianRing O'] [IsLocalRing O']
    [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Field F] [Algebra O' O] [Algebra O F] [Algebra O' F] [IsScalarTower O' O F]
    [IsFractionRing O F] [IsFractionRing O' F]
    [IsLocalHom (algebraMap O' O)] [Module.Flat O' O]
    (hinj : Function.Injective (algebraMap O' O))
    (π : O') (hπ0 : π ≠ 0) (hπ : (Ideal.span {π}).IsPrime) :
    Function.Bijective (algebraMap O' O) := by sorry
