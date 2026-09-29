-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_mapDomain_sp_zeros_sub_algebraMap_eq_and_mapDomain_sp_poles_eq_of_coe_eq_jqModC
-- name    : ModularCurve.JHPlaceSpecialization.mapDomain_sp_zeros_sub_algebraMap_eq_and_mapDomain_sp_poles_eq_of_coe_eq_jqModC
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/e18ed8a7-48a8-593e-9154-43c45de5acee
-- title:
--   Specialisation of the zero and polar divisors of j
-- statement:
--   Fix a prime $p$ and a nonzero level $M$ with $p \mid M$ but $p^2 \nmid M$, so that $M/p$ is nonzero, and fix a subgroup $H \le (\mathbb{Z}/M)^\times$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$ in the sense that $p$ is a nonunit of $A$, with residue field $\kappa$ of characteristic $p$ and algebraically closed, and let $\mathrm{Psp}$ be a `JHPlaceSpecialization` packet for these data: it provides a map $\mathrm{sp}$ from places of $F' := \overline{\mathbb{Q}}\,$-base change of the level-$(M/p)$ modular function field $\mathrm{xHFunctionFieldBar}\,(M/p)\,(\mathrm{infSubgroup}\ p\ M\ H)$ to places of $\bar F' := \mathrm{qExpFunctionFieldC}\ \kappa\ (\Gamma N\ p\ M\ H)$, a map on degree-zero divisor classes, and the compatibilities recorded in that structure ($q$-expansion compatibility of order functions, surjectivity of $\mathrm{sp}$, realisability of pushed-forward divisors, inertia- and Frobenius-equivariance, and compatibility with $\mathrm{Pic}^0$). The assertion is: for all $x \in F'$ and $\bar x \in \bar F'$ whose Laurent series are the $j$-expansion $\mathrm{jqModC}$ over $\overline{\mathbb{Q}}$ and over $\kappa$ respectively, two things hold. First, for every $a \in A$ and every divisor $Z$ on $F'$ with $Z(v) = \max(v.\mathrm{ord}(x - a), 0)$ at every place $v$, the pushforward $\mathrm{Finsupp.mapDomain}\ \mathrm{sp}\ Z$ satisfies, at every place $v'$ of $\bar F'$ over $\kappa$, $(\mathrm{sp}_* Z)(v') = \max(v'.\mathrm{ord}(\bar x - \bar a), 0)$, where $\bar a$ is the residue of $a$. Second, for every divisor $\mathrm{Pl}$ with $\mathrm{Pl}(v) = \max(-v.\mathrm{ord}\,x, 0)$ at every $v$, one has $(\mathrm{sp}_*\mathrm{Pl})(v') = \max(-v'.\mathrm{ord}\,\bar x, 0)$ at every $v'$. Here places are valuation subrings containing the base field, proper and with principal ideals, and $\mathrm{ord}$ is the associated normalised integer valuation.
--
--   This is the statement that reduction along a place specialisation sends the divisor of zeros of $j - a$ and the polar divisor of $j$ on the level-$(M/p)$ modular curve exactly to the corresponding zero and polar divisors of $\bar\jmath - \bar a$ and $\bar\jmath$ in characteristic $p$ — the divisor-theoretic form of good reduction of the $j$-line. It is the common source of the two readings `ord_pos_sp_sub_algebraMap_of_ord_pos` and `ord_sp_neg_of_forall_ord_sub_algebraMap_le`, and is used in the construction of de Rham models at $p$ for $X_H$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_mapDomain_sp_zeros_sub_algebraMap_eq_and_mapDomain_sp_poles_eq_of_coe_eq_jqModC.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing
open AlgebraicCurve
open ModularCurve
open scoped MatrixGroups

theorem ModularCurve.JHPlaceSpecialization.mapDomain_sp_zeros_sub_algebraMap_eq_and_mapDomain_sp_poles_eq_of_coe_eq_jqModC
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
    (Psp : JHPlaceSpecialization p M H hpM A) :
    ∀ (x : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) (xb : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
      ((x : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) →
      ((xb : JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)) : LaurentSeries (ResidueField ↥A)) = jqModC (ResidueField ↥A) →
      (∀ (a : ↥A) (Z : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))),
          (∀ v, Z v = max (v.ord (x - algebraMap (AlgebraicClosure ℚ) _ (a : AlgebraicClosure ℚ))) 0) →
          ∀ v' : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
            Finsupp.mapDomain Psp.sp Z v' = max (v'.ord (xb - algebraMap (ResidueField ↥A) _ (IsLocalRing.residue ↥A a))) 0) ∧
      (∀ (Pl : Divisor (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))),
          (∀ v, Pl v = max (-v.ord x) 0) →
          ∀ v' : Place (ResidueField ↥A) (JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)),
            Finsupp.mapDomain Psp.sp Pl v' = max (-v'.ord xb) 0) := by sorry
