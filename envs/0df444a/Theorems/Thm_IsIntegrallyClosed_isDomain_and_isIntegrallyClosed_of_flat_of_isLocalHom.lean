-- Prove2me | Theorems.Thm_IsIntegrallyClosed_isDomain_and_isIntegrallyClosed_of_flat_of_isLocalHom
-- name    : IsIntegrallyClosed.isDomain_and_isIntegrallyClosed_of_flat_of_isLocalHom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/1261257e-9be2-537e-a967-2d625d8a8084
-- title:
--   Normality descends along a flat local ring homomorphism
-- statement:
--   Let $R$ and $S$ be commutative rings, both local, with $S$ an integral domain that is integrally closed in its field of fractions, and let $f \colon R \to S$ be a ring homomorphism which is flat (i.e. $S$, viewed as an $R$-module via $f$, is flat) and local, in the sense that $f$ carries the maximal ideal of $R$ into the maximal ideal of $S$. The conclusion is the conjunction of two assertions: $R$ is an integral domain, and $R$ is integrally closed, i.e. every element of $\operatorname{Frac} R$ that is integral over $R$ already lies in the image of $R$. Thus normality of a local ring descends along a flat local homomorphism from a normal local ring, with no Noetherian or finiteness hypothesis on either ring.
--
--   This is one direction of faithfully flat descent of normality, in the local form used for stalks: if $X \to Y$ is flat and $X$ is normal at a point above $y$, then $\mathcal{O}_{Y,y}$ is a normal domain. It is invoked in the construction of integrally closed local models and in statements identifying local rings of affine models with localisations, in particular in the descent of semistable models along base change to an intermediate level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsIntegrallyClosed_isDomain_and_isIntegrallyClosed_of_flat_of_isLocalHom.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem IsIntegrallyClosed.isDomain_and_isIntegrallyClosed_of_flat_of_isLocalHom
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S] [IsDomain S]
    [IsIntegrallyClosed S] (f : R →+* S) (hf : f.Flat) [IsLocalHom f] :
    IsDomain R ∧ IsIntegrallyClosed R := by sorry
