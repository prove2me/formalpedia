-- Prove2me | Theorems.Thm_IsLocalRing_ringKrullDim_adicCompletion_maximalIdeal_eq
-- name    : IsLocalRing.ringKrullDim_adicCompletion_maximalIdeal_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/98c6d99d-651e-5d33-98de-b2598ed80ac2
-- title:
--   Krull dimension is preserved by adic completion
-- statement:
--   Let $R$ be a commutative ring which is Noetherian and local, with maximal ideal $\mathfrak m =$ `IsLocalRing.maximalIdeal R`. Form the $\mathfrak m$-adic completion `AdicCompletion (IsLocalRing.maximalIdeal R) R`, that is, the inverse limit of the quotients $R/\mathfrak m^n$ in Mathlib's sense. The assertion is the equality of Krull dimensions $$\operatorname{ringKrullDim}\bigl(\widehat R\bigr) = \operatorname{ringKrullDim} R,$$ where `ringKrullDim` is the Krull dimension of the prime spectrum as an element of `WithBot ℕ∞` (so the equality also covers the degenerate cases, with both sides $\bot$ when the ring is trivial and both sides possibly infinite a priori). No further hypotheses are imposed: locality and the Noetherian condition on $R$ are the only assumptions, and the local structure of the completion is not assumed but supplied by the cited results.
--
--   This is the standard fact that the $\mathfrak m$-adic completion of a Noetherian local ring has the same dimension as the ring itself. It is used in the project wherever a dimension bound is to be transported between a local ring and its completion, for instance to deduce $\dim \widehat{\mathcal O}_{X,z} \le 2$ from $\dim \mathcal O_{X,z} \le 2$ at points of integral models of modular curves, and is cited by the results on local rings of completions lying over a given prime.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_ringKrullDim_adicCompletion_maximalIdeal_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsLocalRing.ringKrullDim_adicCompletion_maximalIdeal_eq
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    ringKrullDim (AdicCompletion (IsLocalRing.maximalIdeal R) R) = ringKrullDim R := by sorry
