-- Prove2me | Theorems.Thm_IsLocalRing_isDiscreteValuationRing_of_nonempty_adicCompletion_ringEquiv_powerSeries
-- name    : IsLocalRing.isDiscreteValuationRing_of_nonempty_adicCompletion_ringEquiv_powerSeries
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:59.02392+00:00
-- url     : https://prove2.me/theorems/4762a38e-98ff-52f2-b543-91f904a0377c
-- title:
--   Noetherian local ring with completion k[[X]] is a DVR
-- statement:
--   Let $A$ be a commutative ring (in universe $u$) that is local and Noetherian, let $\mathfrak m$ denote its maximal ideal, and let $k$ be a field (in an independent universe $v$). Assume that the type of ring isomorphisms between the $\mathfrak m$-adic completion $\mathrm{AdicCompletion}\ \mathfrak m\ A$ of $A$ and the formal power series ring $k[[X]]$ in one variable over $k$ is nonempty, i.e. that at least one such isomorphism exists (the hypothesis is given as a `Nonempty` assertion rather than as a chosen isomorphism). The conclusion is the existential statement that there is a domain structure on $A$ — that is, $A$ has no zero divisors and is nontrivial — such that, relative to it, $A$ is a discrete valuation ring. The packaging as `∃ _ : IsDomain A, IsDiscreteValuationRing A` is forced by the fact that the predicate `IsDiscreteValuationRing` presupposes an `IsDomain` instance; mathematically it asserts that $A$ is a domain and a discrete valuation ring.
--
--   This is the descent of regularity in dimension one from the completion to the ring itself: a Noetherian local ring whose $\mathfrak m$-adic completion is a power series ring in one variable over a field is a discrete valuation ring. It is used in the criterion [`AlgebraicGeometry.smoothOfRelativeDimension_one_of_forall_nonempty_adicCompletion_stalk_ringEquiv_powerSeries`](thm.html#AlgebraicGeometry.smoothOfRelativeDimension_one_of_forall_nonempty_adicCompletion_stalk_ringEquiv_powerSeries), which recognises smoothness of relative dimension one from the shape of the completed local rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsLocalRing_isDiscreteValuationRing_of_nonempty_adicCompletion_ringEquiv_powerSeries.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open IsLocalRing

theorem IsLocalRing.isDiscreteValuationRing_of_nonempty_adicCompletion_ringEquiv_powerSeries
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (k : Type v) [Field k]
    (e : Nonempty (AdicCompletion (maximalIdeal A) A ≃+* PowerSeries k)) :
    ∃ _ : IsDomain A, IsDiscreteValuationRing A := by sorry
