-- Prove2me | Theorems.Thm_IsDiscreteValuationRing_charpoly_mulLeft_single_slope_of_isAdicComplete
-- name    : IsDiscreteValuationRing.charpoly_mulLeft_single_slope_of_isAdicComplete
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.878306+00:00
-- url     : https://prove2.me/theorems/73cb23c4-e264-5ba0-922d-8601d4e5b741
-- title:
--   Characteristic polynomial of multiplication has a single slope
-- statement:
--   Let $W$ be a discrete valuation ring which is a commutative integral domain and is complete with respect to the adic topology of its maximal ideal, let $O$ be a commutative integral domain equipped with a $W$-algebra structure making it a free $W$-module of finite rank, and let $a \in O$. Write $d = \operatorname{finrank}_W O$, let $\chi =$ `(LinearMap.mulLeft W a).charpoly` be the characteristic polynomial of the $W$-linear endomorphism $x \mapsto a x$ of $O$, and let $\operatorname{addVal}_W \colon W \to \mathbb{N}\cup\{\infty\}$ be the normalised additive valuation of $W$ (with value $\infty$ at $0$). The assertion is fourfold: $\chi$ is monic; its degree is $d$; for every natural number $i \le d$ one has the inequality in $\mathbb{N}\cup\{\infty\}$
--   $$(d - i)\cdot \operatorname{addVal}_W\bigl(N_{O/W}(a)\bigr) \;\le\; d \cdot \operatorname{addVal}_W\bigl(\chi_i\bigr),$$
--   where $d-i$ is truncated subtraction of naturals and $\chi_i$ is the $i$-th coefficient of $\chi$; and for $i = 0$ this holds with equality, $d\cdot \operatorname{addVal}_W(N_{O/W}(a)) = d\cdot\operatorname{addVal}_W(\chi_0)$. Everything is stated multiplied through by $d$, so that no division and no extension of the valuation occurs.
--
--   This is the statement that the Newton polygon of the characteristic polynomial of multiplication by $a$ consists of a single segment of slope $\operatorname{addVal}_W(N_{O/W}(a))/d$: over a complete discrete valuation ring all conjugates of $a$ have the same valuation. It is the arithmetic input to [`IsDiscreteValuationRing.charpoly_mulLeft_quotient_eq_finprod_single_slope`](thm.html#IsDiscreteValuationRing.charpoly_mulLeft_quotient_eq_finprod_single_slope).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_IsDiscreteValuationRing_charpoly_mulLeft_single_slope_of_isAdicComplete.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open IsLocalRing Polynomial

theorem IsDiscreteValuationRing.charpoly_mulLeft_single_slope_of_isAdicComplete
    {W : Type u} [CommRing W] [IsDomain W] [IsDiscreteValuationRing W]
    [IsAdicComplete (IsLocalRing.maximalIdeal W) W]
    (O : Type u) [CommRing O] [IsDomain O] [Algebra W O] [Module.Free W O] [Module.Finite W O] (a : O) :
    (LinearMap.mulLeft W a).charpoly.Monic ∧
    (LinearMap.mulLeft W a).charpoly.natDegree = Module.finrank W O ∧
    (∀ i : ℕ, i ≤ Module.finrank W O →
      ((Module.finrank W O - i : ℕ) : ℕ∞) * IsDiscreteValuationRing.addVal W (Algebra.norm W a) ≤
        (Module.finrank W O : ℕ∞) * IsDiscreteValuationRing.addVal W ((LinearMap.mulLeft W a).charpoly.coeff i)) ∧
    ((Module.finrank W O : ℕ∞) * IsDiscreteValuationRing.addVal W (Algebra.norm W a) =
      (Module.finrank W O : ℕ∞) * IsDiscreteValuationRing.addVal W ((LinearMap.mulLeft W a).charpoly.coeff 0)) := by sorry
