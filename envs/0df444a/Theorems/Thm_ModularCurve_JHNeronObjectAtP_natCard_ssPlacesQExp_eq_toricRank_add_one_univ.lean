-- Prove2me | Theorems.Thm_ModularCurve_JHNeronObjectAtP_natCard_ssPlacesQExp_eq_toricRank_add_one_univ
-- name    : ModularCurve.JHNeronObjectAtP.natCard_ssPlacesQExp_eq_toricRank_add_one_univ
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.315379+00:00
-- url     : https://prove2.me/theorems/6bdba05c-b86a-521b-a623-913c48d8ce52
-- title:
--   Supersingular places over any algebraically closed field of characteristic p
-- statement:
--   Let $p$ be a prime and $M$ a positive integer with $p \mid M$ and $M/p$ positive, and let $H$ be a subgroup of $(\mathbb{Z}/M)^{\times}$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}} =$ `AlgebraicClosure ℚ` lying over $p$ in the sense of [`ValuationSubring.LiesOverPrime`](def/FLTPrelim_Ramification.html#L16), i.e. $p$ is a non-unit of $A$, and assume its residue field $\kappa(A)$ has characteristic $p$ and is algebraically closed. Let $\Lambda$ be level data `JHNeronObjectAtP.LevelData p M H hpM A` (a morphism $\sigma_A$ from $\operatorname{Spec} A$ to the base, compatible with the generic point, a scheme $X$ over the base with a relative group law and identifications of the generic and special fibres of points with $J_H(M/p)$-points and with $\mathrm{Pic}^0$ of the reduction), and let $O$ be a `JHNeronObjectAtP p M H hpM A hA Λ`, i.e. a smooth, separated, quasi-compact, surjective commutative relative group scheme over the base with connected fibres whose generic-fibre points are identified $J_H(M)$-equivariantly and Galois-equivariantly, carrying Hecke endomorphisms and the further data recorded in that structure, and with an associated natural number `O.toricRank`. Let $K$ be any algebraically closed field of characteristic $p$. Then the number of elements of the set [`ModularCurve.ssPlacesQExp K Γ p`](def/ModularCurve_XHDifferentialsModL.html#L27) of places $v$ of the $q$-expansion function field of $\Gamma =$ [`CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)`](def/CohCarrier_Level.html#L133) over $K$ (the congruence subgroup attached to the image of $H$ in $(\mathbb{Z}/(M/p))^{\times}$) satisfying the predicate `IsSSPlaceQExp K Γ p` equals `O.toricRank + 1`. Here a place is a proper valuation subring of the function field containing the image of $K$ which is a principal ideal ring.
--
--   This is the count of supersingular points on the modular curve of level $M/p$ and character group $H$ in characteristic $p$, equated with one more than the toric rank of the special fibre of the Néron object of $J_H(M)$ at $p$ (the graph-theoretic description of the totally degenerate fibre at a prime exactly dividing the level). The universe-polymorphic field $K$ allows the count to be used at an arbitrary algebraically closed coefficient field, as is needed downstream in the Serre dlog/abel–Jacobi bridge arguments.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHNeronObjectAtP_natCard_ssPlacesQExp_eq_toricRank_add_one_univ.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_XHDifferentialsModL

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing

theorem ModularCurve.JHNeronObjectAtP.natCard_ssPlacesQExp_eq_toricRank_add_one_univ
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Λ : JHNeronObjectAtP.LevelData p M H hpM A) (O : JHNeronObjectAtP p M H hpM A hA Λ)
    (K : Type*) [Field K] [IsAlgClosed K] [CharP K p] :
    Nat.card ↥(ModularCurve.ssPlacesQExp K (CohCarrier.GammaH (M / p) (ModularCurve.infSubgroup p M H hpM)) p) = O.toricRank + 1 := by sorry
