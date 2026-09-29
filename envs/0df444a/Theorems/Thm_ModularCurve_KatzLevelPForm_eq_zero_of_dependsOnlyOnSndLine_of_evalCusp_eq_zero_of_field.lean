-- Prove2me | Theorems.Thm_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero_of_field
-- name    : ModularCurve.KatzLevelPForm.eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero_of_field
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/ea15322c-e0bb-5fb0-83e3-b7c1433a07a1
-- title:
--   q-expansion principle for Γ₀(p)-type Katz level-p forms
-- statement:
--   Let $K$ be a field, $p$ an odd prime which is invertible in $K$ (i.e. $p \neq 2$ and $(p : K) \neq 0$), $\zeta$ a unit of $K$ and $k$ an integer. Write $W =$ [`ModularCurve.tateBase K p`](def/ModularCurve_TateSlots.html#L46) for the Tate curve `tateLaurent K` over $K((q))$ transported along the ring homomorphism `qExpand K p` that multiplies exponents by $p$, and let $D =$ [`ModularCurve.cuspData K p ζ ![1,0] ![0,1]`](def/ModularCurve_KatzLevelPCusps.html#L71) be the level-$p$ data over $K((q))$ whose first point is `cuspPoint` for the vector $![1,0]$, namely the toric point `tateToricPoint K p ζ`, and whose second point is `cuspPoint` for $![0,1]$, namely `nonToricPoint K p 1 1`. Assume `IsLevelPStructure W p D`: both points satisfy the affine Weierstrass equation of $W$, both $x$-coordinates are roots of $W.\mathrm{pre}\Psi_p$, and both of the elements $\prod_{a=1}^{(p-1)/2}\bigl(x \cdot (W.\Psi\mathrm{Sq}\,a)(x_0) - (W.\Phi\,a)(x_0)\bigr)$ obtained by taking $(x_0,x)$ to be the two $x$-coordinates in either order are units. Let $G$ be a Katz level-$p$ form of weight $k$ over $K$, i.e. a rule attaching to every $K$-algebra $A$, every Weierstrass curve $W'$ over $A$ with $W'.\Delta$ a unit and every level-$p$ structure $D'$ on $W'$ an element of $A$, compatibly with $K$-algebra maps and scaling by $(u^{-k})$ under variable changes $(u,r,s,t)$. Assume `G.DependsOnlyOnSndLine`: the value of $G$ is unchanged when the level-$p$ structure $D'$ is replaced by another one $D''$ on the same curve whose second $x$-coordinate satisfies `InLine`, i.e. $x_{Q''} \cdot (W'.\Psi\mathrm{Sq}\,a)(x_{Q'}) = (W'.\Phi\,a)(x_{Q'})$ for some $1 \le a \le (p-1)/2$. If the value of $G$ on $W$ (whose discriminant is a unit by `isUnit_Δ_tateBase`) at the above cusp data is $0$, then $G = 0$.
--
--   This is the $q$-expansion principle over a field base for Katz forms of full level $p$ that factor through the line spanned by the second point, so for forms of $\Gamma_0(p)$-type: vanishing at the single cusp given by the Tate curve with parameter $q^p$ together with the pair (toric point with parameter $\zeta$, non-toric point) forces the form to vanish identically. It is the field case underlying the version of the statement proved for more general base rings, and rests on the vanishing criterion at the generic Weierstrass curve together with the transitivity, up to the $\Gamma_0(p)$-relation `InLine`, of the Galois action on the roots of $\mathrm{pre}\Psi_p$ over the generic function field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero_of_field.lean

import Mathlib
import Definitions.Def_ModularForm_KatzLevelOne
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPCusps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem ModularCurve.KatzLevelPForm.eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero_of_field
    {K : Type u} [Field K] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp : (p : K) ≠ 0)
    (ζ : Kˣ) {k : ℤ}
    (hc : ModularCurve.IsLevelPStructure (ModularCurve.tateBase K p) p
      (ModularCurve.cuspData K p ζ ![1, 0] ![0, 1]))
    (G : ModularCurve.KatzLevelPForm K p k) (hG : G.DependsOnlyOnSndLine)
    (h0 : G.toFun (ModularCurve.tateBase K p) (ModularCurve.isUnit_Δ_tateBase K p) _ hc = 0) :
    G = 0 := by sorry
