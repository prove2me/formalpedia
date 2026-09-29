-- Prove2me | Theorems.Thm_IsRegularLocalRing_isRegularRing_of_ringKrullDim_le_two
-- name    : IsRegularLocalRing.isRegularRing_of_ringKrullDim_le_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:00.858323+00:00
-- url     : https://prove2.me/theorems/a807842c-fc34-5f2b-b240-0605110ce29b
-- title:
--   Regular local rings of Krull dimension ≤ 2 are regular
-- statement:
--   Let $R$ be a commutative ring (in the bottom universe) that is a regular local ring in Mathlib's sense, and suppose its Krull dimension, taken as an element of $\mathrm{WithBot}\,\mathbb{N}^\infty$, satisfies $\dim R \le 2$. The conclusion is that $R$ satisfies `IsRegularRing`; by `isRegularRing_iff` this says precisely that for every prime ideal $\mathfrak p$ of $R$ the localisation $R_{\mathfrak p} =$ `Localization.AtPrime` $\mathfrak p$ is again a regular local ring. Thus the hypothesis of regularity at the closed point alone, in the presence of the dimension bound, propagates to regularity at every point of $\operatorname{Spec} R$. No hypotheses beyond the commutative ring structure, regular locality and the bound $\dim R \le 2$ are imposed; in particular noetherianity is part of the regular local hypothesis, and the bound is stated for the Krull dimension of $R$ itself, not for the residue characteristic or any completeness assumption.
--
--   This is the low-dimensional case of the theorem that a regular local ring is a regular ring, i.e. that regularity localises; it is used in the construction of regular two-dimensional local rings of the required shape, being cited in the passage to complete discrete valuation rings and in the power series construction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsRegularLocalRing_isRegularRing_of_ringKrullDim_le_two.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem IsRegularLocalRing.isRegularRing_of_ringKrullDim_le_two
    (R : Type) [CommRing R] [IsRegularLocalRing R] (hdim : ringKrullDim R ≤ 2) :
    IsRegularRing R := by sorry
