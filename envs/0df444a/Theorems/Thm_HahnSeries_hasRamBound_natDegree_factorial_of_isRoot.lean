-- Prove2me | Theorems.Thm_HahnSeries_hasRamBound_natDegree_factorial_of_isRoot
-- name    : HahnSeries.hasRamBound_natDegree_factorial_of_isRoot
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:55.058405+00:00
-- url     : https://prove2.me/theorems/abe0820d-9542-5179-9033-2824fce83cf1
-- title:
--   Newton–Puiseux bound: roots have exponents in tfrac1n!ℤ
-- statement:
--   Let $K$ be an algebraically closed field of characteristic $0$, and work in the field $\mathbb{K} =$ `HahnSeries ℚ K` of Hahn series with value group $\mathbb{Q}$ and coefficients in $K$. Let $p \in \mathbb{K}[Y]$ be a nonzero polynomial each of whose coefficients $p_i$ ($i \in \mathbb{N}$) satisfies [`HahnSeries.HasRamBound 1`](def/HahnSeries_RamificationBound.html#L32), that is, the support of $p_i$ is contained in the set of rationals of the form $k/1$ with $k \in \mathbb{Z}$; so every coefficient of $p$ is a Laurent series, with integral exponents. Let $y \in \mathbb{K}$ be a root of $p$, i.e. $p$ evaluated at $y$ is $0$. The conclusion is that $y$ satisfies [`HahnSeries.HasRamBound n!`](def/HahnSeries_RamificationBound.html#L32) where $n =$ `p.natDegree`: the support of $y$ is contained in the set of rationals of the form $k/n!$ with $k \in \mathbb{Z}$, i.e. $\operatorname{supp}(y) \subseteq \tfrac{1}{n!}\mathbb{Z}$. Note that the hypothesis on the coefficients is imposed for all natural numbers $i$, and that the denominator bound is stated as the factorial of the degree rather than as an unspecified or optimal integer, so the statement carries no existential quantifier.
--
--   This is the Newton–Puiseux theorem in the form asserting that an element of the Hahn series field $K((t^{\mathbb{Q}}))$ which is algebraic over the Laurent series field $K((t))$ is a Puiseux series, with an explicit bound $n!$ on the ramification of its exponents. It is used in the construction and comparison of places on modular curves, being cited by [`ModularCurve.exists_place_of_emb`](thm.html#ModularCurve.exists_place_of_emb), [`ModularCurve.samePlace_iff_exists_hahnTwist`](thm.html#ModularCurve.samePlace_iff_exists_hahnTwist) and [`ModularCurve.card_eq_natCard_quot_samePlace_of_forall_mem_iff_pos_ord`](thm.html#ModularCurve.card_eq_natCard_quot_samePlace_of_forall_mem_iff_pos_ord).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_HahnSeries_hasRamBound_natDegree_factorial_of_isRoot.lean

import Mathlib
import Definitions.Def_HahnSeries_RamificationBound

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem HahnSeries.hasRamBound_natDegree_factorial_of_isRoot
    {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    {p : Polynomial (HahnSeries ℚ K)} (hp : p ≠ 0)
    (hcoeff : ∀ i : ℕ, HahnSeries.HasRamBound 1 (p.coeff i))
    {y : HahnSeries ℚ K} (hy : p.IsRoot y) :
    HahnSeries.HasRamBound p.natDegree.factorial y := by sorry
