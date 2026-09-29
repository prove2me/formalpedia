-- Prove2me | Theorems.Thm_MvPowerSeries_subst_add_sum_smul_eq_add_sum_smul_mul_subst_pderiv
-- name    : MvPowerSeries.subst_add_sum_smul_eq_add_sum_smul_mul_subst_pderiv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:56.228905+00:00
-- url     : https://prove2.me/theorems/4e66054d-6139-5d6f-b4f3-104a767e706b
-- title:
--   First-order expansion of substitution along a square-zero increment
-- statement:
--   Let $R$ be a commutative ring and let $\sigma$, $\tau$, $\kappa$ be finite index types. Given a family of scalars $j : \kappa \to R$ with $j_k\, j_{k'} = 0$ for all $k, k'$, a multivariate power series $f \in R[[X_i]]_{i \in \sigma}$, a family $A : \sigma \to R[[X_t]]_{t \in \tau}$ all of whose members have vanishing constant coefficient, and an arbitrary family $B : \sigma \to \kappa \to R[[X_t]]_{t \in \tau}$, the assertion is the exact identity
--   $$\mathrm{subst}\big(i \mapsto A_i + \textstyle\sum_k j_k \cdot B_{i k}\big)\, f \;=\; \mathrm{subst}\,A\, f \;+\; \sum_{k} j_k \cdot \sum_{i} B_{i k} \cdot \mathrm{subst}\,A\,(\partial_i f)$$
--   in $R[[X_t]]_{t \in \tau}$, where $\mathrm{subst}$ denotes substitution of the given families into a power series and $\partial_i f =$ `pderivLin i f` is the $R$-linear operator whose coefficient at a multi-index $d$ is $(d_i + 1)$ times the coefficient of $f$ at $d + \delta_i$, i.e. the formal partial derivative of $f$ in the $i$-th variable. No hypothesis on the constant coefficients of the $B_{ik}$ is imposed.
--
--   This is the first-order Taylor expansion of substitution into a power series in the direction of an increment whose coefficients lie in a square-zero family of scalars, the error terms of order $\ge 2$ being annihilated by the relations $j_k j_{k'} = 0$. It is used in the theory of deformations of multivariate formal group laws, for instance in the construction and uniqueness of shifts and of isomorphisms between deformations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvPowerSeries_subst_add_sum_smul_eq_add_sum_smul_mul_subst_pderiv.lean

import Mathlib
import Definitions.Def_FormalGroup_NSeries

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MvPowerSeries

theorem MvPowerSeries.subst_add_sum_smul_eq_add_sum_smul_mul_subst_pderiv
    {R : Type} [CommRing R] {σ : Type} [Fintype σ] {τ : Type} [Fintype τ] {κ : Type} [Fintype κ]
    (j : κ → R) (hj : ∀ k k', j k * j k' = 0)
    (f : MvPowerSeries σ R)
    (A : σ → MvPowerSeries τ R) (hA : ∀ i, MvPowerSeries.constantCoeff (A i) = 0)
    (B : σ → κ → MvPowerSeries τ R) :
    MvPowerSeries.subst (fun i => A i + ∑ k, j k • B i k) f =
      MvPowerSeries.subst A f + ∑ k, j k • ∑ i, B i k * MvPowerSeries.subst A (MvPowerSeries.pderivLin i f) := by sorry
