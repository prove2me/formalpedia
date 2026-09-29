-- Prove2me | Theorems.Thm_ModularCurve_JHPlaceSpecialization_le_sum_ramificationIndexAlong_filter_not_isInftySide_fiberAlong
-- name    : ModularCurve.JHPlaceSpecialization.le_sum_ramificationIndexAlong_filter_not_isInftySide_fiberAlong
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:40.860483+00:00
-- url     : https://prove2.me/theorems/84d95e7e-936a-5f72-ab3e-63148f9335bb
-- title:
--   Non-∞-side ramification above b sums to at least p
-- statement:
--   Fix a prime $p$ and a nonzero level $M$ with $p \mid M$ but $p^2 \nmid M$, and a subgroup $H \le (\mathbb{Z}/M)^\times$ containing every unit that reduces to $1$ in $(\mathbb{Z}/(M/p))^\times$; assume $M/p \neq 0$. Let $A$ be a valuation subring of $\overline{\mathbb{Q}}$ lying over $p$, in the sense that $p$ is a nonunit of $A$. Write $F_M$ and $F_{M/p}$ for the intermediate fields `xHFunctionFieldBar M H` and `xHFunctionFieldBar (M/p) (infSubgroup p M H hpM)` of the Laurent series field over $\overline{\mathbb{Q}}$, the second taken for the image subgroup of $H$ under reduction. Let $\alpha : F_{M/p} \to F_M$ be an integral $\overline{\mathbb{Q}}$-algebra map which is the identity on underlying Laurent series, and assume principal divisors exist on $F_M$. Then for every place $b$ of $F_{M/p}$ over $\overline{\mathbb{Q}}$, the sum of the ramification indices $e(W \mid_\alpha b)$, taken over those places $W$ in the fibre of $b$ along $\alpha$ for which the predicate `JHPlaceSpecialization.IsInftySide` fails — that is, $W$ is not cuspidal in the sense of `IsCuspidal`, or else there is no $\tau \in A$ with residue $1$ at which $W$ takes the value $x'/x^p$ for $x, x'$ realising the $q$-expansions $j(q)$ and $j(q^p)$ — is at least $p$.
--
--   This is the lower bound for the ramification of the first degeneracy map $X_H(M) \to X_{H'}(M/p)$ concentrated away from the $\infty$-component of the fibre, the function-field counterpart of the local description of the two sheets of the Hecke correspondence at $p$. It feeds the companion statement [`ModularCurve.JHPlaceSpecialization.sum_ramificationIndexAlong_filter_isInftySide_fiberAlong_eq_one_of_forall_ord_sub_nonpos`](thm.html#ModularCurve.JHPlaceSpecialization.sum_ramificationIndexAlong_filter_isInftySide_fiberAlong_eq_one_of_forall_ord_sub_nonpos), which pins the $\infty$-side contribution to $1$; together they supply the ramification bookkeeping used in the analysis of places of the modular curve above $p$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JHPlaceSpecialization_le_sum_ramificationIndexAlong_filter_not_isInftySide_fiberAlong.lean

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

theorem ModularCurve.JHPlaceSpecialization.le_sum_ramificationIndexAlong_filter_not_isInftySide_fiberAlong
    (p M : ℕ) [Fact p.Prime] [NeZero M] (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) (hpM2 : ¬ p ^ 2 ∣ M)
    (hHp : ∀ u : (ZMod M)ˣ, ZMod.unitsMap (Nat.div_dvd_of_dvd hpM) u = 1 → u ∈ H) [NeZero (M / p)]
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (α : ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM)) →ₐ[AlgebraicClosure ℚ] ↥(xHFunctionFieldBar M H))
    (hα : α.IsIntegral)
    (hα_coe : ∀ u, ((α u : ↥(xHFunctionFieldBar M H)) : LaurentSeries (AlgebraicClosure ℚ)) = (u : LaurentSeries (AlgebraicClosure ℚ)))
    [HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar M H)]
    (b : Place (AlgebraicClosure ℚ) ↥(xHFunctionFieldBar (M / p) (infSubgroup p M H hpM))) :
    (p : ℤ) ≤ ∑ W ∈ (Place.fiberAlong α hα b).filter (fun W => ¬ JHPlaceSpecialization.IsInftySide (p := p) (M := M) (H := H) (A := A) W),
        (W.ramificationIndexAlong α : ℤ) := by sorry
