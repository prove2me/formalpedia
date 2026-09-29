-- Prove2me | Theorems.Thm_IsLocalRing_quotient_of_ne_top
-- name    : IsLocalRing.quotient_of_ne_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/8a56f540-3a98-5f27-aecf-75144a0cec37
-- title:
--   A proper quotient of a local ring is local
-- statement:
--   Let $A$ be a commutative ring which is local in Mathlib's sense (`IsLocalRing`: $A$ is nontrivial and the non-units form an ideal, equivalently $A$ has a unique maximal ideal), and let $I$ be an ideal of $A$ with $I \neq \top$, i.e. $I$ is a proper ideal. The theorem asserts that the quotient ring $A \mathbin{/} I$ is again a local ring in the same sense. The properness hypothesis is exactly what is needed for the conclusion: it is equivalent to $A \mathbin{/} I$ being nontrivial, and without it the quotient would be the zero ring, which is excluded from `IsLocalRing`. No further hypotheses on $I$ are imposed; in particular $I$ need not be contained in any prescribed ideal beyond being proper, and the maximal ideal of $A \mathbin{/} I$ is the image of the maximal ideal of $A$.
--
--   Elementary bookkeeping about local rings, used to keep quotients of coefficient rings within the category of local rings. It is invoked in the verification that the flat, ordinary and strict-ordinary conditions on Galois deformations are deformation conditions, where quotients of local coefficient rings must again be local.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_quotient_of_ne_top.lean

import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.Ideal.Quotient.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem IsLocalRing.quotient_of_ne_top
    {A : Type} [CommRing A] [IsLocalRing A] (I : Ideal A) (hI : I ≠ ⊤) :
    IsLocalRing (A ⧸ I) := by sorry
