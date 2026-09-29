-- Prove2me | Theorems.Thm_HenselianLocalRing_of_isIntegral_of_isLocalRing
-- name    : HenselianLocalRing.of_isIntegral_of_isLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.342414+00:00
-- url     : https://prove2.me/theorems/ef59b6d8-61d2-5c62-92f6-a8527bffef02
-- title:
--   Integral local extensions of henselian local rings are henselian
-- statement:
--   Let $R$ be a commutative ring which is a henselian local ring, and let $S$ be a commutative ring which is a local ring, equipped with an $R$-algebra structure making $S$ integral over $R$ (every element of $S$ satisfies a monic polynomial with coefficients in $R$). The conclusion is that $S$ is itself a henselian local ring: $S$ is local, and for every monic polynomial $f \in S[X]$ and every $a_0 \in S$ with $f(a_0)$ in the maximal ideal of $S$ and $f'(a_0)$ a unit of $S$, there exists $a \in S$ with $f(a) = 0$ and $a - a_0$ in the maximal ideal of $S$. No finiteness is assumed on $S$ as an $R$-module, only integrality; in particular $S$ need not be noetherian, and no separatedness or residue-field hypothesis enters.
--
--   This is the standard fact that a local ring integral over a henselian local ring is henselian (Hensel's lemma propagates along integral local extensions). Within the formalisation it supplies henselianity of local rings arising as integral extensions, and is used in the construction of supersingular discrete valuation rings and local charts on modular curves of full level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HenselianLocalRing_of_isIntegral_of_isLocalRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

theorem HenselianLocalRing.of_isIntegral_of_isLocalRing
    {R : Type u} [CommRing R] [HenselianLocalRing R]
    {S : Type v} [CommRing S] [IsLocalRing S] [Algebra R S] [Algebra.IsIntegral R S] :
    HenselianLocalRing S := by sorry
