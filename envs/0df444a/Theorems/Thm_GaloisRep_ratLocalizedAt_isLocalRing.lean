-- Prove2me | Theorems.Thm_GaloisRep_ratLocalizedAt_isLocalRing
-- name    : GaloisRep.ratLocalizedAt.isLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:47.88569+00:00
-- url     : https://prove2.me/theorems/4789a35c-c357-56ad-a999-0090934980e3
-- title:
--   ℤ₍ₚ₎ is a local ring
-- statement:
--   Let $p$ be a natural number which is prime. Consider the subring [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8) of $\mathbb{Q}$ whose underlying set consists of those rationals $q$ whose denominator $q.\mathrm{den}$ (the reduced positive denominator) is coprime to $p$; this set is closed under multiplication, addition and negation and contains $0$ and $1$, since the denominator of a sum or product of two rationals divides the product of their denominators. The assertion is that this subring is a local ring in Mathlib's sense, i.e. it is a nontrivial commutative ring in which the non-units form an ideal. Concretely, the ring in question is the localisation $\mathbb{Z}_{(p)}$ of $\mathbb{Z}$ at the prime $p$, realised inside $\mathbb{Q}$, and the conclusion is the `IsLocalRing` instance for it.
--
--   This is the elementary fact that $\mathbb{Z}_{(p)}$, the ring of rationals with denominator prime to $p$, is local; no Galois representation, elliptic curve or modular form occurs in it. It is invoked throughout the part of the development dealing with finite flat group schemes and Dieudonné modules over $\mathbb{Z}_{(p)}$, where local-ring hypotheses on the base are required.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_GaloisRep_ratLocalizedAt_isLocalRing.lean

import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem GaloisRep.ratLocalizedAt.isLocalRing
    {p : ℕ} (hp : p.Prime) : IsLocalRing (GaloisRep.ratLocalizedAt p) := by sorry
