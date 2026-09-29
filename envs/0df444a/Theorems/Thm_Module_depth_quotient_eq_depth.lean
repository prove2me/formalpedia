-- Prove2me | Theorems.Thm_Module_depth_quotient_eq_depth
-- name    : Module.depth_quotient_eq_depth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.610395+00:00
-- url     : https://prove2.me/theorems/9d5d7951-6cc8-5035-818e-cda95f772e07
-- title:
--   Depth is unchanged under passing to a quotient ring
-- statement:
--   Let $R$ be a commutative local ring, let $I \subseteq R$ be an ideal such that the quotient ring $R/I$ is again local, and let $N$ be an abelian group carrying both an $R$-module structure and an $R/I$-module structure, compatibly in the sense that the $R$-action on $N$ is obtained from the $R/I$-action along the quotient map $R \to R/I$ (a scalar tower). For a commutative local ring $A$ and an $A$-module $M$, the quantity $\mathtt{Module.depth}\ A\ M \in \mathbb{N}\cup\{\infty\}$ is defined as the supremum of the lengths of those finite lists $s$ of elements of $A$ all of whose entries lie in the maximal ideal of $A$ and which are weakly regular sequences on $M$; in particular the supremum is taken over a set that always contains the empty list, and it is $\infty$ when arbitrarily long such sequences exist. The assertion is the equality
--   $$\operatorname{depth}_{R/I}(N) = \operatorname{depth}_{R}(N)$$
--   of these two elements of $\mathbb{N}\cup\{\infty\}$.
--
--   This is the standard fact that depth may be computed over any local ring through which the module action factors, the two maximal ideals matching under $R \to R/I$ and weak regularity of a sequence being a condition on the action alone. It is used to transport depth computations between a local ring and its quotients, and is invoked in the proof that for a Cohen–Macaulay local ring of given dimension the Krull dimension of a quotient and the height of the corresponding ideal add up correctly.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Module_depth_quotient_eq_depth.lean

import Mathlib
import Definitions.Def_Patching_SystemTypes

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open IsLocalRing RingTheory

theorem Module.depth_quotient_eq_depth
    {R : Type*} [CommRing R] [IsLocalRing R] (I : Ideal R) [IsLocalRing (R ⧸ I)]
    (N : Type*) [AddCommGroup N] [Module R N] [Module (R ⧸ I) N] [IsScalarTower R (R ⧸ I) N] :
    Module.depth (R ⧸ I) N = Module.depth R N := by sorry
