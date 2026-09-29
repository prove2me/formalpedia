-- Prove2me | Theorems.Thm_IsLocalRing_two_le_ringKrullDim_adicCompletion_of_two_le
-- name    : IsLocalRing.two_le_ringKrullDim_adicCompletion_of_two_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/0a02e75a-c7a5-5ec8-bcc8-c3eb351992b7
-- title:
--   Krull dimension ≥ 2 passes to the 𝔪-adic completion
-- statement:
--   Let $R$ be a commutative ring which is Noetherian and local, with maximal ideal $\mathfrak m =$ `IsLocalRing.maximalIdeal R`, and suppose that the Krull dimension of $R$, measured by `ringKrullDim` as an element of $\mathbb{N}_\infty$ adjoined a bottom element (so that the empty spectrum has dimension $\bot$), satisfies $2 \le \dim R$. The conclusion is that the $\mathfrak m$-adic completion `AdicCompletion (IsLocalRing.maximalIdeal R) R`, regarded as a commutative ring, also satisfies $2 \le \operatorname{ringKrullDim}$. Thus only the inequality in one direction, and only at the threshold $2$, is asserted: no equality $\dim \widehat R = \dim R$ and no statement about completions with respect to other ideals.
--
--   This is the easy half of the standard fact that $\mathfrak m$-adic completion of a Noetherian local ring preserves Krull dimension, specialised to the threshold $2$. It supplies the dimension hypothesis for the crossing-model results on adic completions of local rings and stalks, for instance [`AlgebraicGeometry.exists_ringEquiv_adicCompletion_stalk_crossingScheme_uvCrossingModel_of_mem_asIdeal`](thm.html#AlgebraicGeometry.exists_ringEquiv_adicCompletion_stalk_crossingScheme_uvCrossingModel_of_mem_asIdeal).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_two_le_ringKrullDim_adicCompletion_of_two_le.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsLocalRing.two_le_ringKrullDim_adicCompletion_of_two_le
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] (h : 2 ≤ ringKrullDim R) :
    2 ≤ ringKrullDim (AdicCompletion (IsLocalRing.maximalIdeal R) R) := by sorry
