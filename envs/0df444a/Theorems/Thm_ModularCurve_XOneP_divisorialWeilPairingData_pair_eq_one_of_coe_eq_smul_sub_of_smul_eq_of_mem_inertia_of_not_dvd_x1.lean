-- Prove2me | Theorems.Thm_ModularCurve_XOneP_divisorialWeilPairingData_pair_eq_one_of_coe_eq_smul_sub_of_smul_eq_of_mem_inertia_of_not_dvd_x1
-- name    : ModularCurve.XOneP.divisorialWeilPairingData_pair_eq_one_of_coe_eq_smul_sub_of_smul_eq_of_mem_inertia_of_not_dvd_x1
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:47.601084+00:00
-- url     : https://prove2.me/theorems/612a906a-e1c8-5547-b846-43a6879040b3
-- title:
--   Inertia annihilates the Weil pairing on σ z - z
-- statement:
--   Fix $N \ge 1$, a prime $p$, and a valuation subring $\mathfrak{P}$ of $\overline{\mathbf{Q}}$ lying over $p$ in the sense that the image of $p$ lies in the nonunits of $\mathfrak{P}$; fix also $n \ge 1$ with $p \nmid n$. Let $F$ be [`ModularCurve.x1FunctionFieldBar N`](def/ModularCurve_X1.html#L182), the base change to $\overline{\mathbf{Q}}$ of the function field `x1FunctionField N` inside Laurent series, and assume `HasPrincipalDivisors` for $F$ over $\overline{\mathbf{Q}}$: every nonzero $f \in F$ has a divisor, supported on the places of $F$ over $\overline{\mathbf{Q}}$, whose coefficient at $v$ is $\operatorname{ord}_v f$ and whose degree is $0$. Let $W$ be a `DivisorialWeilPairingData` of level $n$, i.e. a function `pair` on pairs of $n$-torsion classes in $\mathrm{Pic}^0(F) =$ `JOne N` with values in $\overline{\mathbf{Q}}$, agreeing with the pairing attached to each Weil datum and satisfying the stated moving property for representing divisors. Let $\sigma$ be a $\mathbf{Q}$-automorphism of $\overline{\mathbf{Q}}$ lying in the image of the inertia subgroup of $\mathfrak{P}$ inside its decomposition subgroup, and let $z, y, x$ be $n$-torsion classes in $\mathrm{Pic}^0(F)$ such that $\sigma \cdot y = y$ and $x = \sigma \cdot z - z$ in `JOne N`. Then $W.\mathrm{pair}\,(x, y) = 1$.
--
--   This is the prime-to-$p$ Galois step in the analysis of the inertia action on the $n$-torsion of the Jacobian of $X_1(N)$: the pairing of an inertia coboundary $\sigma z - z$ against an inertia-fixed class is trivial. It is used in the Weil-datum formulation [`ModularCurve.XOneP.weilDatum_pairing_eq_one_of_proj_eq_zero_of_points_valuationSubring_of_curveModel_igusa_twoChartModel_x1_mul`](thm.html#ModularCurve.XOneP.weilDatum_pairing_eq_one_of_proj_eq_zero_of_points_valuationSubring_of_curveModel_igusa_twoChartModel_x1_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_XOneP_divisorialWeilPairingData_pair_eq_one_of_coe_eq_smul_sub_of_smul_eq_of_mem_inertia_of_not_dvd_x1.lean

import Mathlib
import Definitions.Def_ModularCurve_X1
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_AlgebraicCurve_FunctionFieldWeilPairingDivisorial

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve
open scoped MatrixGroups

theorem ModularCurve.XOneP.divisorialWeilPairingData_pair_eq_one_of_coe_eq_smul_sub_of_smul_eq_of_mem_inertia_of_not_dvd_x1
    (N : ℕ) [NeZero N]
    (p : ℕ) [Fact p.Prime] (Pl : ValuationSubring (AlgebraicClosure ℚ)) (hPl : Pl.LiesOverPrime p)
    (n : ℕ) [NeZero n] (hpn : ¬ p ∣ n)
    [AlgebraicCurve.HasPrincipalDivisors (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar N)]
    (W : AlgebraicCurve.DivisorialWeilPairingData (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar N) n)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ Pl.inertiaSubgroupIn ℚ)
    (z y x : AlgebraicCurve.Pic0.torsion (AlgebraicClosure ℚ) ↥(ModularCurve.x1FunctionFieldBar N) n)
    (hyσ : σ • (y : ModularCurve.JOne N) = y)
    (hx : (x : ModularCurve.JOne N) = σ • (z : ModularCurve.JOne N) - z) :
    W.pair x y = 1 := by sorry
