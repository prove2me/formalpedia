-- Prove2me | Theorems.Thm_ModularCurve_SSLevelDatum_heckeLaws_of_prime_ne_of_not_dvd
-- name    : ModularCurve.SSLevelDatum.heckeLaws_of_prime_ne_of_not_dvd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:46.379182+00:00
-- url     : https://prove2.me/theorems/cf60686f-2cda-596b-952c-5b4cb8c01f13
-- title:
--   Hecke laws for the two-level supersingular degeneracy datum
-- statement:
--   Let $M \ge 1$ and let $q'$, $s$ be primes with $s \neq q'$, $q' \nmid M$ and $s \nmid M$. Let $A$ be a valuation subring of $\overline{\mathbb Q}$ whose residue field $\kappa =$ `IsLocalRing.ResidueField A` has characteristic $q'$, and assume the sets $\mathrm{ssPlaces}\,q'\,(Ms)\,\kappa$ and $\mathrm{ssPlaces}\,q'\,M\,\kappa$ — the places of the function fields $\mathrm{modularFunctionFieldC}\,\kappa\,(Ms)$, resp. level $M$, satisfying `IsSupersingularPlace` at $q'$ — are finite. Let $X$ be an `SSLevelDatum q' κ M s`: witnesses that $\mathrm{jqNModC}\,\kappa\,M$ and $\mathrm{jqNModC}\,\kappa\,s$ lie in the level-$Ms$ field, integrality of the two level maps `levelAlphaC`, `levelBetaC` and of all maps `heckeAlphaC`, `heckeBetaC`, the fact that restriction along the two level maps carries supersingular places of level $Ms$ to supersingular places of level $M$, an Atkin–Lehner automorphism in the sense of `IsAtkinLehnerLevelAut` preserving the supersingular places, and modular polynomial data satisfying the Kronecker congruence. The conclusion is `X.HeckeLaws`: the matrices $X.\mathrm{edgeHecke}\,\ell$ pairwise commute, the matrices $X.\mathrm{vertexHecke}\,\ell$ pairwise commute, for each prime $\ell \neq s$ both pushforwards $\mathrm{jointDelta}\,X.\mathrm{degeneracyData}\,i$ ($i \in \{0,1\}$, along the two degeneracy maps) intertwine $X.\mathrm{edgeHecke}\,\ell$ with $X.\mathrm{vertexHecke}\,\ell$ on $\mathbb Z$-valued functions on the supersingular places of level $Ms$, and for every prime $\ell$ the joint kernel of the two pushforwards is stable under $X.\mathrm{edgeHecke}\,\ell$.
--
--   This is the width-free core of the two-level Hecke laws for supersingular points in characteristic $q'$ at levels $Ms \rightrightarrows M$: commutativity at each level, compatibility of the degeneracy pushforwards with Hecke operators away from the switch prime $s$, and stability of the character group of the torus (Ribet's group $Y$). It is invoked in the construction of the degeneracy datum together with its row-sum and adjointness laws, and in the comparison of toric monodromy spans used for level lowering.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_SSLevelDatum_heckeLaws_of_prime_ne_of_not_dvd.lean

import Definitions.Def_ModularCurve_SSDegeneracyHecke

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open ModularCurve

theorem ModularCurve.SSLevelDatum.heckeLaws_of_prime_ne_of_not_dvd
    (M s q' : ℕ) [NeZero M] [Fact q'.Prime] [Fact s.Prime]
    (hsq' : s ≠ q') (hq'M : ¬ q' ∣ M) (hsM : ¬ s ∣ M)
    (A : ValuationSubring (AlgebraicClosure ℚ))
    [DecidableEq (IsLocalRing.ResidueField ↥A)] [CharP (IsLocalRing.ResidueField ↥A) q']
    [Fintype ↥(ssPlaces q' (M * s) (IsLocalRing.ResidueField ↥A))]
    [Fintype ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A))]
    [DecidableEq ↥(ssPlaces q' M (IsLocalRing.ResidueField ↥A))]
    (X : SSLevelDatum q' (IsLocalRing.ResidueField ↥A) M s) :
    X.HeckeLaws := by sorry
