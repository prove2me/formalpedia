-- Prove2me | Theorems.Thm_MvFormalGroup_nilEval_eq_adicEval_of_pow_succ_eq_bot
-- name    : MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:55.856965+00:00
-- url     : https://prove2.me/theorems/aed0e527-777b-5b82-a9ef-093b02287312
-- title:
--   Truncated and J-adic evaluation agree when Jⁿ⁺¹=0
-- statement:
--   Let $B$ be a commutative ring, $\sigma$ a finite type with decidable equality, and $B'$ a commutative $B$-algebra. Let $J$ be an ideal of $B'$ and $n$ a natural number such that $J^{n+1}=\bot$. Let $\varphi$ be a multivariate formal power series in the variables indexed by $\sigma$ with coefficients in $B$, and let $s:\sigma\to B'$ be a tuple with $s_i\in J$ for every $i$. Then the two evaluations of $\varphi$ at $s$ coincide: on the one hand [`MvFormalGroup.nilEval n φ s`](def/AlgebraicGeometry_FormalGroupAlongSection.html#L15), which is the image of $s$ under the $B$-algebra evaluation map applied to the truncation `MvPowerSeries.trunc' B` of $\varphi$ at the multidegree $(n,\dots,n)$, i.e. the polynomial consisting of the monomials of $\varphi$ all of whose exponents are at most $n$; on the other hand [`MvFormalGroup.adicEval J s φ`](def/MvFormalGroup_PointsV2.html#L20), which is `MvPowerSeries.eval₂ (algebraMap B B') s φ` formed with $B$ carrying the discrete uniform structure and $B'$ carrying the $J$-adic structure, i.e. the limit of the $J$-adically convergent sum $\sum_d \varphi_d s^d$.
--
--   This is the dictionary between the two ways of evaluating a formal power series at a tuple of nilpotent coordinates: truncated polynomial evaluation, used for formal coordinates along a section of a group scheme, and adic evaluation, used for the group of points of a formal group with values in an ideal. It is invoked throughout the treatment of formal $\mathcal{O}_D$-modules and of fake elliptic curves in the Čerednik–Drinfel'd setting, where coordinates lie in an ideal with a prescribed nilpotency bound.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_MvFormalGroup_nilEval_eq_adicEval_of_pow_succ_eq_bot.lean

import Mathlib
import Definitions.Def_MvFormalGroup_PointsV2
import Definitions.Def_AlgebraicGeometry_FormalGroupAlongSection

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem MvFormalGroup.nilEval_eq_adicEval_of_pow_succ_eq_bot
    {B : Type} [CommRing B] {σ : Type} [Fintype σ] [DecidableEq σ]
    {B' : Type} [CommRing B'] [Algebra B B'] (J : Ideal B') (n : ℕ) (hJ : J ^ (n + 1) = ⊥)
    (φ : MvPowerSeries σ B) (s : σ → B') (hs : ∀ i, s i ∈ J) :
    MvFormalGroup.nilEval n φ s = MvFormalGroup.adicEval J s φ := by sorry
