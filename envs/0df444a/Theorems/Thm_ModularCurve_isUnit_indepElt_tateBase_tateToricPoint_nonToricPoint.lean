-- Prove2me | Theorems.Thm_ModularCurve_isUnit_indepElt_tateBase_tateToricPoint_nonToricPoint
-- name    : ModularCurve.isUnit_indepElt_tateBase_tateToricPoint_nonToricPoint
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/3259de43-e38d-5aba-ba1c-764c6af29f33
-- title:
--   Independence element of toric and slot points is a unit
-- statement:
--   Let $K$ be a commutative ring, let $p$ be a natural number with $p \neq 0$, let $c, c' \in K^{\times}$, and assume that $1 - c$ is a unit of $K$. Let $j$ be a natural number with $0 < j < p$. Consider the Weierstrass curve `tateBase K p` over the field of Laurent series $K((q))$: it is the Tate Weierstrass curve $y^2 + xy = x^3 + a_4 x + a_6$ with integral coefficients, base changed to $K$ and then transported along the ring homomorphism `qExpand K p`, which multiplies all exponents by $p$ (substitution $q \mapsto q^p$). Let $x_P$ be the first component of `tateToricPoint K p c`, the Laurent series coming from the power series whose constant coefficient is $c \cdot \mathrm{inverse}(1-c)^2$ and whose $m$-th coefficient for $m > 0$ is $\sum_{d \mid m,\, p \mid d} (m/d)\big(c^{m/d} + c^{-m/d}\big) - 2\big[p \mid m\big]\sum_{e \mid m/p} e$, and let $x_Q$ be the first component of `nonToricPoint K p c' j`, the Laurent series coming from the power series `slotSubst K p c' j tateUnivX`, obtained by substituting the family `slotFamily K p c' j` into the two-variable series `tateUnivX`. Then the element
--   $$\prod_{a=1}^{\lfloor (p-1)/2 \rfloor}\big(x_Q \cdot (\Psi^2_a)(x_P) - \Phi_a(x_P)\big),$$
--   the value `indepElt (tateBase K p) p x_P x_Q` formed from the division polynomials $\Psi^2_a$ and $\Phi_a$ of `tateBase K p`, is a unit in $K((q))$.
--
--   The element in question is the non-degeneracy ("independence") quantity whose invertibility expresses that the toric point with parameter $c$ and the point in the $j$-th slot with parameter $c'$ generate independent order-$p$ subgroups, so that the pair is a level-$p$ structure on the Tate curve over Laurent series. It feeds the cusp computations for Katz level-$p$ forms, being used by the verification that `tateBase` together with the Mazur cusp data carries a level-$p$ structure and by the vanishing criterion for such forms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isUnit_indepElt_tateBase_tateToricPoint_nonToricPoint.lean

import Mathlib
import Definitions.Def_ModularCurve_TateSlots
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPCusps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem ModularCurve.isUnit_indepElt_tateBase_tateToricPoint_nonToricPoint
    (K : Type u) [CommRing K] (p : ℕ) [NeZero p] (c c' : Kˣ) (hc : IsUnit (1 - (c : K)))
    (j : ℕ) (hj : 0 < j) (hjp : j < p) :
    IsUnit (ModularCurve.indepElt (ModularCurve.tateBase K p) p
      (ModularCurve.tateToricPoint K p c).1 (ModularCurve.nonToricPoint K p c' j).1) := by sorry
