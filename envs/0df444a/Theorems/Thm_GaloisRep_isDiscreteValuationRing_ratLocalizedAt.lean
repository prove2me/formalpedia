-- Prove2me | Theorems.Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt
-- name    : GaloisRep.isDiscreteValuationRing_ratLocalizedAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/4bc554af-5370-5d1b-afba-baee09b5e3c5
-- title:
--   ℤ₍ₚ₎ is a discrete valuation ring
-- statement:
--   For a natural number $p$ together with a hypothesis that $p$ is prime, the subring [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ is a discrete valuation ring. Here [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) is defined as the set of rational numbers $q$ whose denominator $q.\mathrm{den}$ (the positive denominator of the reduced representation) is coprime to $p$; this set is shown to be a subring of $\mathbb{Q}$ using the divisibility of the denominator of a sum and of a product by the product of the denominators. The conclusion is Mathlib's predicate `IsDiscreteValuationRing` for this subring, i.e. it is a local principal ideal domain whose maximal ideal is nonzero. For $p$ prime this ring is the usual localisation $\mathbb{Z}_{(p)}$, and the statement asserts nothing about non-prime $p$ (indeed the conclusion fails for $p = 1$, where the ring is $\mathbb{Q}$, and for composite $p$).
--
--   This is the classical fact that the localisation of $\mathbb{Z}$ at a nonzero prime ideal $(p)$ is a discrete valuation ring. It supplies the discrete-valuation-ring structure on the base $\mathbb{Z}_{(p)}$, over which results stated for an abstract discrete valuation ring with fraction field $\mathbb{Q}$ — integral models of curves, finite flat group schemes and the flatness condition at $p$ — are specialised; it is cited widely throughout the development.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_isDiscreteValuationRing_ratLocalizedAt.lean

import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRep.isDiscreteValuationRing_ratLocalizedAt (p : ℕ) (hp : p.Prime) :
    IsDiscreteValuationRing (GaloisRep.ratLocalizedAt p) := by sorry
