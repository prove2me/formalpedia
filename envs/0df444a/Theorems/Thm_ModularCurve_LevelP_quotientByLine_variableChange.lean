-- Prove2me | Theorems.Thm_ModularCurve_LevelP_quotientByLine_variableChange
-- name    : ModularCurve.LevelP.quotientByLine_variableChange
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:42.499921+00:00
-- url     : https://prove2.me/theorems/0e492ca6-4396-5bb0-b3b0-db5efaf2061b
-- title:
--   Vélu's x-only quotient commutes with Weierstrass variable changes
-- statement:
--   Let $A$ be a commutative ring, let $W$ be a Weierstrass curve over $A$, let $p$ be a natural number, let $C$ be an admissible change of Weierstrass coordinates over $A$, with unit scaling factor $C.u$ and translation parameter $C.r$, and let $x \in A$. Assume that for every natural number $a$ in the interval $[1,(p-1)/2]$ (truncated subtraction and division on $\mathbb{N}$) the value $(W.\Psi\mathrm{Sq}\,a).\mathrm{eval}\,x$ of the squared $a$-th division polynomial at $x$ is a unit of $A$. The conclusion is the equality of Weierstrass curves
--   $$\mathrm{quotientByLine}\,(C \bullet W)\,p\,\bigl(C.u^{-1}{}^{2}\,(x - C.r)\bigr) \;=\; C \bullet \bigl(\mathrm{quotientByLine}\,W\,p\,x\bigr),$$
--   where $C \bullet {-}$ denotes Mathlib's action of a variable change on Weierstrass curves, and where $\mathrm{quotientByLine}\,W\,p\,x$ is the curve with the same $a_1, a_2, a_3$ as $W$, with $a_4 = W.a_4 - 5T$ and with $a_6 = W.a_6 - W.b_2\,T - 7V$; here $T = \sum_{a=1}^{(p-1)/2}\bigl(6\,\xi_a^2 + W.b_2\,\xi_a + W.b_4\bigr)$ and $V = \sum_{a=1}^{(p-1)/2}\bigl(W.\Psi_2\mathrm{Sq}.\mathrm{eval}\,\xi_a + \xi_a(6\,\xi_a^2 + W.b_2\,\xi_a + W.b_4)\bigr)$, with $\xi_a = \mathrm{smulX}\,W\,a\,x$ the abscissa attached to the $a$-fold multiple of a point with abscissa $x$. In short, replacing $x$ by its transform $u^{-2}(x-r)$ under $C$ turns the Vélu quotient data of $C \bullet W$ into the $C$-transform of the Vélu quotient data of $W$.
--
--   This is the equivariance of Vélu's quotient construction, in its $x$-only coefficient form, under admissible changes of Weierstrass coordinates: forming the quotient by the line spanned by a point of abscissa $x$ commutes with the action of $(u,r,s,t)$. It is used in the construction of Katz-style forms on $\Gamma_0(p)$, being cited by [`ModularForm.exists_katzGamma0Form_evalCusp_eq_of_five_le`](thm.html#ModularForm.exists_katzGamma0Form_evalCusp_eq_of_five_le), where the quotient curve must be shown to depend on the pair (curve, point) only up to coordinate change, with the expected weights.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_LevelP_quotientByLine_variableChange.lean

import Mathlib
import Definitions.Def_ModularCurve_KatzLevelPQuotient

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

theorem ModularCurve.LevelP.quotientByLine_variableChange
    {A : Type u} [CommRing A] (W : WeierstrassCurve A) (p : ℕ) (C : WeierstrassCurve.VariableChange A)
    {x : A} (h : ∀ a ∈ Finset.Icc 1 ((p - 1) / 2), IsUnit ((W.ΨSq a).eval x)) :
    ModularCurve.LevelP.quotientByLine (C • W) p (((C.u⁻¹ : Aˣ) : A) ^ 2 * (x - C.r)) =
      C • ModularCurve.LevelP.quotientByLine W p x := by sorry
