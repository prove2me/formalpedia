-- Prove2me | Theorems.Thm_IsLocalRing_isArtinianRing_quotient_maximalIdeal_pow
-- name    : IsLocalRing.isArtinianRing_quotient_maximalIdeal_pow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/1bace214-c0b5-5208-a2d0-2ba2fc2caaa1
-- title:
--   A/𝔪^{m+1} is Artinian for Noetherian local A
-- statement:
--   Let $A$ be a commutative ring (in the smallest universe) which is local, in the sense of Mathlib's `IsLocalRing`, and Noetherian, and let $m$ be a natural number. Writing $\mathfrak{m} =$ `IsLocalRing.maximalIdeal A` for the maximal ideal of $A$, the assertion is that the quotient ring $A / \mathfrak{m}^{m+1}$ is Artinian, i.e. satisfies `IsArtinianRing`: it is an Artinian module over itself, so its ideals satisfy the descending chain condition. Note that the exponent is written in the form $m+1$, so the statement covers exactly the positive powers of $\mathfrak{m}$; the case of the zeroth power, where the quotient is the zero ring, is not part of the statement.
--
--   This is the standard fact that a Noetherian local ring becomes Artinian after dividing by a positive power of its maximal ideal, so that the finite-level quotients $A/\mathfrak{m}^{m+1}$ are legitimate Artinian test objects. It is used in the verification of the deformation conditions `flatCondition`, `ordinaryCondition` and `strictOrdinaryCondition`, whose defining properties are tested on Artinian coefficient algebras while the continuity arguments are phrased over the quotients $A/\mathfrak{m}^{m+1}$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_isArtinianRing_quotient_maximalIdeal_pow.lean

import Mathlib.RingTheory.Artinian.Ring

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem IsLocalRing.isArtinianRing_quotient_maximalIdeal_pow
    {A : Type} [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (m : ℕ) :
    IsArtinianRing (A ⧸ IsLocalRing.maximalIdeal A ^ (m + 1)) := by sorry
