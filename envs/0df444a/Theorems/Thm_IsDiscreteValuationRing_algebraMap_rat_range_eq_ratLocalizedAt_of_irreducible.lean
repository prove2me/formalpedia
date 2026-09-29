-- Prove2me | Theorems.Thm_IsDiscreteValuationRing_algebraMap_rat_range_eq_ratLocalizedAt_of_irreducible
-- name    : IsDiscreteValuationRing.algebraMap_rat_range_eq_ratLocalizedAt_of_irreducible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/fdb5599c-98b9-50ef-a680-90bd0e6ad320
-- title:
--   Image of a DVR with fraction field ℚ and uniformiser p
-- statement:
--   Let $R$ be a commutative ring which is a domain and a discrete valuation ring, equipped with an algebra structure over $\mathbb{Q}$-wards, i.e. with a map $R \to \mathbb{Q}$ making $\mathbb{Q}$ a fraction field of $R$, and let $p$ be a prime natural number whose image $(p : R)$ is irreducible in $R$. Then the range of the structure morphism $R \to \mathbb{Q}$, as a subring of $\mathbb{Q}$, coincides with [`GaloisRep.ratLocalizedAt p`](def/GaloisRep_Flat.html#L8), the subring of $\mathbb{Q}$ whose carrier is the set of rationals $q$ whose denominator $q.\mathrm{den}$ (the positive denominator of the reduced fraction) is coprime to $p$; that subring structure records that this set contains $0$ and $1$ and is closed under addition, multiplication and negation. Thus the conclusion is an equality of subrings of $\mathbb{Q}$ identifying the image of $R$ with the localisation $\mathbb{Z}_{(p)}$ described by the coprimality-of-denominators condition.
--
--   This is the classification of discrete valuation rings with fraction field $\mathbb{Q}$, pinned down by the choice of uniformiser: a rational prime $p$ being irreducible in $R$ forces the image of $R$ in $\mathbb{Q}$ to be $\mathbb{Z}_{(p)}$. It is used by [`HopfAlgebra.exists_finiteFlat_dvr_of_ratLocalizedAt_of_irreducible`](thm.html#HopfAlgebra.exists_finiteFlat_dvr_of_ratLocalizedAt_of_irreducible) in setting up the local integral structures attached to the Galois representations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDiscreteValuationRing_algebraMap_rat_range_eq_ratLocalizedAt_of_irreducible.lean

import Mathlib
import Definitions.Def_GaloisRep_Flat

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem IsDiscreteValuationRing.algebraMap_rat_range_eq_ratLocalizedAt_of_irreducible
    (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    [Algebra R ℚ] [IsFractionRing R ℚ]
    (p : ℕ) [Fact p.Prime] (hp : Irreducible (p : R)) :
    (algebraMap R ℚ).range = GaloisRep.ratLocalizedAt p := by sorry
