-- Prove2me | Theorems.Thm_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero
-- name    : ModularCurve.KatzLevelPForm.eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/b9926b5e-fd8e-5233-bd36-95a7e681ae70
-- title:
--   q-expansion principle for Γ₀(p)-type Katz forms
-- statement:
--   Let $R_0$ be a commutative ring, $p$ a prime with $p \neq 2$ and $p$ invertible in $R_0$, and let $R$ be a commutative $R_0$-algebra which is faithfully flat as an $R_0$-module (both rings in the same universe). Let $\zeta$ be a unit of $R$ with $\sum_{i<p}\zeta^{i}=0$, and let $k \in \mathbb{Z}$. Write $W$ for `tateBase R p`, the Tate Weierstrass curve over the Laurent series ring $R((q))$ pulled back along $q \mapsto q^{p}$, and let $D$ be `cuspData R p ζ ![1,0] ![0,1]`, whose first point is the toric point attached to $\zeta$ and whose second is the non-toric point attached to $q$. Assume $D$ is a level-$p$ structure on $W$ in the sense of `IsLevelPStructure`: both points satisfy the affine Weierstrass equation, the polynomial $W.\mathrm{pre\Psi}\,p$ vanishes at both $x$-coordinates, and the two products $\prod_{a=1}^{(p-1)/2}\bigl(x\,\Psi_a^2(x_0)-\Phi_a(x_0)\bigr)$ obtained from the two orderings of the $x$-coordinates are units. Let $G$ be a Katz level-$p$ form of weight $k$ over $R_0$, i.e. a rule assigning to every $R_0$-algebra $A$, every Weierstrass curve over $A$ with unit discriminant and every level-$p$ structure $D$ on it an element of $A$, compatible with $R_0$-algebra maps and scaling by $u^{-k}$ under variable change. Assume $G$ satisfies `DependsOnlyOnSndLine`: its values at two level-$p$ structures $D, D'$ on the same curve agree whenever $x_{Q'}\,\Psi_a^2(x_Q) = \Phi_a(x_Q)$ for some $1 \le a \le (p-1)/2$. If the value of $G$ at $W$ and $D$ vanishes, then $G = 0$.
--
--   This is the $q$-expansion principle for modular forms of weight $k$ on $\Gamma_0(p)$ over a base in which $p$ is invertible: such a form is determined by its expansion at the single cusp given by the Tate curve $\mathrm{Tate}(q^{p})$ with its $\zeta$-point and $q$-point. It is used to produce Katz forms of $\Gamma_0$-type with prescribed value at that cusp, via [`ModularForm.exists_katzGamma0Form_evalCusp_eq_of_five_le`](thm.html#ModularForm.exists_katzGamma0Form_evalCusp_eq_of_five_le).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero.lean

import Mathlib
import Definitions.Def_ModularForm_KatzLevelOne
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPCusps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem ModularCurve.KatzLevelPForm.eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero
    {R₀ : Type u} [CommRing R₀] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp : IsUnit (p : R₀))
    (R : Type u) [CommRing R] [Algebra R₀ R] [Module.FaithfullyFlat R₀ R]
    (ζ : Rˣ) (hζ : ∑ i ∈ Finset.range p, (ζ : R) ^ i = 0) {k : ℤ}
    (hc : ModularCurve.IsLevelPStructure (ModularCurve.tateBase R p) p (ModularCurve.cuspData R p ζ ![1, 0] ![0, 1]))
    (G : ModularCurve.KatzLevelPForm R₀ p k) (hG : G.DependsOnlyOnSndLine)
    (h0 : G.toFun (ModularCurve.tateBase R p) (ModularCurve.isUnit_Δ_tateBase R p) _ hc = 0) : G = 0 := by sorry
