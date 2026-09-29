-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_sum_ramificationIndexAlong_filter_isInftySide_fiberAlong_eq_one_of_forall_ord_sub_nonpos
-- name    : ModularCurve.JHPlaceSpecialization.sum_ramificationIndexAlong_filter_isInftySide_fiberAlong_eq_one_of_forall_ord_sub_nonpos
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/bbf8913d-ad68-5f1a-821f-dfd0dcfd4fd9
-- title:
--   Sum of ramification weights of ∞-side places equals one
-- statement:
--   Let $p$ be a prime and $M$ a nonzero natural number with $p \mid M$ and $p^2 \nmid M$, let $H \le (\mathbf{Z}/M)^\times$ be a subgroup containing every unit whose image under reduction $(\mathbf{Z}/M)^\times \to (\mathbf{Z}/(M/p))^\times$ is $1$, and suppose $M/p \ne 0$. Let $A$ be a valuation subring of $\overline{\mathbf{Q}} =$ `AlgebraicClosure ℚ` with $p$ a non-unit of $A$. Write $F_M =$ `xHFunctionFieldBar M H` and $F_{M/p}$ for the corresponding field at level $M/p$ and subgroup `infSubgroup p M H hpM`, the image of $H$ under that reduction map; both are intermediate fields of $\overline{\mathbf{Q}} \subseteq \overline{\mathbf{Q}}((q))$. Let $\alpha \colon F_{M/p} \to F_M$ be a $\overline{\mathbf{Q}}$-algebra map which is integral and which is the identity on underlying Laurent series, and assume $F_M$ has principal divisors (every nonzero element has a degree-zero divisor given by its orders at all places). Let $b$ be a place of $F_{M/p}$ over $\overline{\mathbf{Q}}$ such that for every $x \in F_{M/p}$ whose Laurent series is `jqModC` and every $a \in A$ one has $\mathrm{ord}_b(x - a) \le 0$. Then the sum of the ramification indices $e(W \mid b)$ along $\alpha$, taken over those $W$ in the fibre of $b$ along $\alpha$ satisfying `JHPlaceSpecialization.IsInftySide` — namely $W$ is cuspidal in the sense of the predicate `IsCuspidal` and, for elements $x, x' \in F_M$ with Laurent series `jqModC` and `qExpand` of `jqModC` at $p$ respectively, $W$ takes at $x'/x^p$ a value lying in $A$ with residue $1$ — equals $1$.
--
--   Over a place $b$ of the level-$(M/p)$ modular function field at which $j$ assumes no $A$-integral value, the fibre along the first degeneracy map splits into an $\infty$-side part and its complement; this is the assertion that the $\infty$-side carries total ramification weight exactly $1$, the expected picture of the two components of the fibre of $X_H(M)$ over a cusp-like point in characteristic $p$ when $p \parallel M$. It feeds the construction and verification of the de Rham model data at $p$ for $X_H(M)$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_sum_ramificationIndexAlong_filter_isInftySide_fiberAlong_eq_one_of_forall_ord_sub_nonpos.lean

import Mathlib
import Definitions.Def_ModularCurve_JHNeronObjectAtP
import Definitions.Def_ModularCurve_JHPlaceSpecialization
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open ModularCurve

open Classical in

theorem ModularCurve.JHPlaceSpecialization.sum_ramificationIndexAlong_filter_isInftySide_fiberAlong_eq_one_of_forall_ord_sub_nonpos
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)]
    (b : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)))
    (hb : ∀ x : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)),
      ((x : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) : LaurentSeries (AlgebraicClosure ℚ)) = jqModC (AlgebraicClosure ℚ) →
      ∀ a : ↥A, b.ord (x - algebraMap (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) (a : AlgebraicClosure ℚ)) ≤ 0) :
    (∑ W ∈ (Place.fiberAlong α hα b).filter (JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A)),
        (W.ramificationIndexAlong α : ℤ)) = 1 := by sorry
