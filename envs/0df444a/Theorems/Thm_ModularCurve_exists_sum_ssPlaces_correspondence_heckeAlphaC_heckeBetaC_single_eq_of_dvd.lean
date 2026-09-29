-- Prove2me | Theorems.Thm_ModularCurve_exists_sum_ssPlaces_correspondence_heckeAlphaC_heckeBetaC_single_eq_of_dvd
-- name    : ModularCurve.exists_sum_ssPlaces_correspondence_heckeAlphaC_heckeBetaC_single_eq_of_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:52.061738+00:00
-- url     : https://prove2.me/theorems/ff4b8f6b-9252-5550-b4da-50e9d9250082
-- title:
--   Constant column sums of β_*α^* on supersingular places
-- statement:
--   Let $M, s, q'$ be natural numbers, with $M$ and $s$ nonzero, $s$ prime and $q'$ prime, subject to $s \neq q'$, $q' \nmid M$ and $s \mid M$. Let $k$ be an algebraically closed field of characteristic $q'$, and assume that the intermediate field $\mathtt{charLDegeneracyRoof}\,k\,M\,s$ of $\mathrm{Laurent}(k)$ — the field generated over $k$ by $j(q)$ and by the functions $j(q^M)$, $j(q^s)$, $j(q^{Ms})$ — has principal divisors, i.e. every nonzero element $f$ of it admits a divisor of degree $0$ whose coefficient at each place $v$ is $v.\mathrm{ord}(f)$. Assume further that the two legs $\mathtt{heckeAlphaC}$ and $\mathtt{heckeBetaC}$ from $\mathtt{modularFunctionFieldC}\,k\,M$ into this roof are integral as ring homomorphisms (the predicates `HeckeAlphaCIntegral` and `HeckeBetaCIntegral`), and that the set $\mathtt{ssPlaces}\,q'\,M\,k$ of places $w$ of $\mathtt{modularFunctionFieldC}\,k\,M$ satisfying the predicate `IsSupersingularPlace` for $q', M$ is finite. Then there is an integer $c$ such that for every supersingular place $x$, the divisor $\beta_*\alpha^*([x])$ — the pullback along $\mathtt{heckeAlphaC}$ of the divisor $1\cdot[x]$ followed by the pushforward along $\mathtt{heckeBetaC}$ — has the property that the sum of its coefficients over all supersingular places $y$ equals $c$; the same $c$ for all $x$.
--
--   This is the statement that the matrix on supersingular places of the correspondence $\beta_*\alpha^*$, the transpose-type companion of the Hecke operator $U_s$ at a prime $s$ dividing the level $M$, has constant column sums (the value exhibited by the proof being the degree of the leg $\alpha$). It feeds the comparison of the Hecke-torsion part of the character lattice of the supersingular component group with a quotient, in [`ModularCurve.SSLevelDatum.finrank_heckeTorsion_ribbonComponentGroup_le_finrank_quotient_of_addEquiv_prod_characterLattice`](thm.html#ModularCurve.SSLevelDatum.finrank_heckeTorsion_ribbonComponentGroup_le_finrank_quotient_of_addEquiv_prod_characterLattice) and its companion equality.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_exists_sum_ssPlaces_correspondence_heckeAlphaC_heckeBetaC_single_eq_of_dvd.lean

import Mathlib
import Definitions.Def_ModularCurve_CharLDegeneracyHecke
import Definitions.Def_ModularCurve_PlaceWidth

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.exists_sum_ssPlaces_correspondence_heckeAlphaC_heckeBetaC_single_eq_of_dvd
    (M s q' : ℕ) [NeZero M] [NeZero s] (hs : s.Prime) [Fact q'.Prime]
    (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : s ∣ M)
    {k : Type*} [Field k] [CharP k q'] [IsAlgClosed k] [DecidableEq k]
    [HasPrincipalDivisors k ↥(charLDegeneracyRoof k M s)]
    (hα : HeckeAlphaCIntegral k M s) (hβ : HeckeBetaCIntegral k M s)
    [Fintype ↥(ssPlaces q' M k)] :
    ∃ c : ℤ, ∀ x : ↥(ssPlaces q' M k),
      ∑ y : ↥(ssPlaces q' M k),
        Divisor.correspondence (heckeAlphaC k M s) (heckeBetaC k M s) hα hβ (Finsupp.single x.1 1) y.1 = c := by sorry
