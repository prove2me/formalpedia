-- Prove2me | Theorems.Thm_ModularCurve_LevelP_quotientByLine_eq_of_inLine
-- name    : ModularCurve.LevelP.quotientByLine_eq_of_inLine
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/27a32988-92ff-5eaf-adf6-b9ae6281fe15
-- title:
--   Vélu's x-only quotient depends only on the line
-- statement:
--   Let $A$ be a commutative ring, $W$ a Weierstrass curve over $A$ with coefficients $a_1,\dots,a_6$, and $p$ a prime with $p \neq 2$ such that $p \cdot \Delta(W)$ is a unit in $A$. Let $x, x' \in A$ be such that the division polynomial $\mathrm{pre}\Psi_p$ of $W$ vanishes at $x$, and suppose that $x$ and $x'$ lie on the same line in the sense of [`ModularCurve.InLine W p x x'`](def/ModularCurve_KatzLevelP.html#L21), i.e. there is a natural number $a$ with $1 \le a \le (p-1)/2$ and $x' \cdot \Psi_a^2(x) = \Phi_a(x)$. Then the two quotient curves [`ModularCurve.LevelP.quotientByLine W p x'`](def/ModularCurve_KatzLevelPQuotient.html#L45) and [`ModularCurve.LevelP.quotientByLine W p x`](def/ModularCurve_KatzLevelPQuotient.html#L45) are equal as Weierstrass curves over $A$. Here `quotientByLine W p x` is the Weierstrass curve with the same $a_1, a_2, a_3$ as $W$ and with $a_4$ replaced by $a_4 - 5t(x)$ and $a_6$ by $a_6 - b_2 t(x) - 7w(x)$, where, writing $x_a$ for the abscissa-multiplication value `smulX W a x`, $t(x) = \sum_{a=1}^{(p-1)/2} (6x_a^2 + b_2 x_a + b_4)$ and $w(x) = \sum_{a=1}^{(p-1)/2} (\Psi_2^2(x_a) + x_a(6x_a^2 + b_2 x_a + b_4))$. Thus the equality asserted is an identity between the two pairs of modified coefficients.
--
--   This is the $x$-only form, over an arbitrary base ring, of the statement that Vélu's quotient of $W$ by a cyclic subgroup of odd prime order $p$ depends only on the subgroup and not on the chosen generator: replacing the abscissa $x$ of a point $Q$ of order $p$ by the abscissa of $[a]Q$ for $1 \le a \le (p-1)/2$ leaves the quotient curve unchanged. It is what makes invariants of the quotient curve, such as its $j$-invariant, functions of the level-$p$ line alone, and it is used in the construction of Katz modular forms on $\Gamma_0(p)$ ([`ModularForm.exists_katzGamma0Form_evalCusp_eq_of_five_le`](thm.html#ModularForm.exists_katzGamma0Form_evalCusp_eq_of_five_le)).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelP_quotientByLine_eq_of_inLine.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ModularCurve.LevelP.quotientByLine_eq_of_inLine
    {A : Type u} [CommRing A] (W : WeierstrassCurve A) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hW : IsUnit ((p : A) * W.Δ)) {x x' : A} (hx : (W.preΨ p).eval x = 0)
    (h : ModularCurve.InLine W p x x') :
    ModularCurve.LevelP.quotientByLine W p x' = ModularCurve.LevelP.quotientByLine W p x := by sorry
