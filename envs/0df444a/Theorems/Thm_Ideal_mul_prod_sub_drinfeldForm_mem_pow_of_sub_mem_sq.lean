-- Prove2me | Theorems.Thm_Ideal_mul_prod_sub_drinfeldForm_mem_pow_of_sub_mem_sq
-- name    : Ideal.mul_prod_sub_drinfeldForm_mem_pow_of_sub_mem_sq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:57.239308+00:00
-- url     : https://prove2.me/theorems/37150842-579e-56e5-8586-1ddf7a0cf2ba
-- title:
--   Product of linear forms congruent to x₀x₁^q-x₀^qx₁ modulo 𝔪^{q+2}
-- statement:
--   Let $q$ be a natural number assumed prime (as a `Fact` instance), let $R$ be a commutative ring and $\mathfrak{m}$ an ideal of $R$ — not assumed maximal — such that the image of $q$ under the canonical map $\mathbb{N}\to R$ lies in $\mathfrak{m}^{q+2}$. Let $x_0,x_1$ be elements of $\mathfrak{m}$, and let $P$ be an arbitrary family of elements of $R$ indexed by $\mathbb{Z}/q$ with the property that for every $c \in \mathbb{Z}/q$ the difference $P(c) - \bigl(x_1 + \overline{c}\,x_0\bigr)$ lies in $\mathfrak{m}^2$, where $\overline{c}$ denotes the image in $R$ of the canonical natural-number representative `c.val` of $c$. The conclusion is the congruence $$x_0 \cdot \prod_{c \in \mathbb{Z}/q} P(c) \;\equiv\; x_0 x_1^{q} - x_0^{q} x_1 \pmod{\mathfrak{m}^{q+2}},$$ i.e. the element $x_0\bigl(\prod_{c} P(c)\bigr) - (x_0x_1^{q} - x_0^{q}x_1)$ belongs to $\mathfrak{m}^{q+2}$.
--
--   This is the congruence, in the shape used for supersingular deformation rings with Drinfeld level structure, identifying the product over the $q$ points of a $q$-torsion configuration — each given only to first order by a linear form $x_1 + c\,x_0$ — with the form $x_0x_1^{q} - x_0^{q}x_1$ modulo $\mathfrak{m}^{q+2}$. It feeds the presentation result [`FormalGroup.IsDrinfeldBasisAdic.exists_ringEquiv_mvPowerSeries_quotient_drinfeldForm_of_isRegularLocalRing`](thm.html#FormalGroup.IsDrinfeldBasisAdic.exists_ringEquiv_mvPowerSeries_quotient_drinfeldForm_of_isRegularLocalRing).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Ideal_mul_prod_sub_drinfeldForm_mem_pow_of_sub_mem_sq.lean

import Mathlib
import Definitions.Def_DrinfeldCurve_LocalChart
import Definitions.Def_FormalGroup_NSeries
import Definitions.Def_FormalGroup_DrinfeldBasis
import Definitions.Def_FormalGroup_PointTransport

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsLocalRing FormalGroup

theorem Ideal.mul_prod_sub_drinfeldForm_mem_pow_of_sub_mem_sq
    (q : ℕ) [Fact q.Prime]
    (R : Type) [CommRing R] (𝔪 : Ideal R) (hq : ((q : ℕ) : R) ∈ 𝔪 ^ (q + 2))
    (x₀ x₁ : R) (hx₀ : x₀ ∈ 𝔪) (hx₁ : x₁ ∈ 𝔪)
    (P : ZMod q → R) (hP : ∀ c : ZMod q, P c - (x₁ + ((c.val : ℕ) : R) * x₀) ∈ 𝔪 ^ 2) :
    x₀ * (∏ c : ZMod q, P c) - (x₀ * x₁ ^ q - x₀ ^ q * x₁) ∈ 𝔪 ^ (q + 2) := by sorry
