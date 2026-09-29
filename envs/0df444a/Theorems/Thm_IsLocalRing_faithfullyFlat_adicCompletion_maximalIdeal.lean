-- Prove2me | Theorems.Thm_IsLocalRing_faithfullyFlat_adicCompletion_maximalIdeal
-- name    : IsLocalRing.faithfullyFlat_adicCompletion_maximalIdeal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/b8e8bb5d-f63d-5c9c-b6fd-428f88385e4f
-- title:
--   Adic completion of a noetherian local ring is faithfully flat
-- statement:
--   Let $R$ be a commutative ring that is noetherian and local, with maximal ideal $\mathfrak m =$ `IsLocalRing.maximalIdeal R`. The theorem asserts that the $\mathfrak m$-adic completion $\widehat R = \varprojlim_n R/\mathfrak m^n$, formed as `AdicCompletion (IsLocalRing.maximalIdeal R) R`, is a faithfully flat $R$-module: it is flat, and moreover tensoring with it detects non-vanishing, in the sense of Mathlib's `Module.FaithfullyFlat` predicate. No further hypotheses are imposed; the conclusion is a statement about $\widehat R$ as an $R$-module (equivalently, about the structure map $R \to \widehat R$, which is the relevant one since $\widehat R$ is an $R$-algebra).
--
--   This is the standard fact that the completion of a noetherian local ring at its maximal ideal is faithfully flat over the ring, allowing properties of $R$ (for instance integral closedness) to be deduced from the corresponding properties of $\widehat R$ by descent. It is used in the local analysis of curve singularities in this development, notably in the normality and crossing-model criteria for local rings arising at nodes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_faithfullyFlat_adicCompletion_maximalIdeal.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsLocalRing.faithfullyFlat_adicCompletion_maximalIdeal
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] :
    Module.FaithfullyFlat R (AdicCompletion (IsLocalRing.maximalIdeal R) R) := by sorry
