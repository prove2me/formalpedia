-- Prove2me | Theorems.Thm_Module_flat_of_maximalIdeal_rTensor_injective_of_isLocalHom
-- name    : Module.flat_of_maximalIdeal_rTensor_injective_of_isLocalHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/94780bca-8332-56fb-acbb-e800d3106779
-- title:
--   Local flatness criterion for a finite module over a local extension
-- statement:
--   Let $A$ and $B$ be commutative noetherian local rings (in the same universe), let $B$ be an $A$-algebra whose structure morphism $A \to B$ is a local homomorphism, i.e. carries the maximal ideal of $A$ into the maximal ideal of $B$, and let $M$ be an abelian group carrying compatible $A$- and $B$-module structures, the $A$-action being the restriction of the $B$-action along $A \to B$, such that $M$ is finitely generated as a $B$-module. Assume that the $A$-linear map obtained from the inclusion $\mathfrak m_A \hookrightarrow A$ of the maximal ideal of $A$ by tensoring with $M$ on the right, $\mathfrak m_A \otimes_A M \to A \otimes_A M$, is injective; equivalently $\operatorname{Tor}_1^A(A/\mathfrak m_A, M) = 0$. Then $M$ is flat as an $A$-module. The hypothesis is thus Tor-vanishing against the residue field of $A$ alone, and the conclusion is flatness, not freeness.
--
--   This is the local criterion of flatness in its Tor-free spelling, in the relative form where the finiteness of $M$ is over a second noetherian local ring $B$ receiving a local homomorphism from $A$; the case $B = A$ is the absolute statement available in Mathlib, where finite presentation over $A$ yields freeness. It is used in the verification that a monomorphism of schemes which admits lifts of points valued in artinian local rings is an open immersion.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_flat_of_maximalIdeal_rTensor_injective_of_isLocalHom.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open TensorProduct IsLocalRing

universe u

theorem Module.flat_of_maximalIdeal_rTensor_injective_of_isLocalHom
    {A B : Type u} [CommRing A] [CommRing B] [IsNoetherianRing A] [IsNoetherianRing B] [IsLocalRing A] [IsLocalRing B]
    [Algebra A B] [IsLocalHom (algebraMap A B)]
    (M : Type u) [AddCommGroup M] [Module A M] [Module B M] [IsScalarTower A B M] [Module.Finite B M]
    (h : Function.Injective (LinearMap.rTensor M (maximalIdeal A).subtype)) :
    Module.Flat A M := by sorry
