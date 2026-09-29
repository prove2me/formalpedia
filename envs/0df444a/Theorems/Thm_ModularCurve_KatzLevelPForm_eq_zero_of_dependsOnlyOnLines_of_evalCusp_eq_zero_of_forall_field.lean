-- Prove2me | Theorems.Thm_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnLines_of_evalCusp_eq_zero_of_forall_field
-- name    : ModularCurve.KatzLevelPForm.eq_zero_of_dependsOnlyOnLines_of_evalCusp_eq_zero_of_forall_field
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/529c5451-5fab-5c70-92b9-00907675e51b
-- title:
--   Vanishing of Katz level-p forms: fields to rings
-- statement:
--   Let $R$ be a commutative ring, $p$ an odd prime with $p$ invertible in $R$, and $\zeta \in R^\times$ a unit with $\sum_{i<p}\zeta^i = 0$; fix a weight $k \in \mathbb{Z}$. Write $T_R$ for `tateBase R p`, the Tate Weierstrass curve over $R((q))$ pulled back along $q \mapsto q^{p}$, and let $D_R =$ `cuspData R p ζ ![0, 1] ![1, 1]` be the level-$p$ datum whose two points are `cuspPoint` for the vectors $(0,1)$ and $(1,1)$, i.e. the non-toric points `nonToricPoint R p (ζ ^ 0) 1` and `nonToricPoint R p (ζ ^ 1) 1`. Assume $D_R$ is a level-$p$ structure on $T_R$: both points satisfy the affine equation, the $x$-coordinates are roots of $\mathrm{pre}\Psi_p$, and both products $\mathrm{indepElt} = \prod_{1 \le a \le (p-1)/2}\bigl(x\,\Psi^2_a(x_0) - \Phi_a(x_0)\bigr)$, taken in either order of the two points, are units. Let $G$ be a Katz level-$p$ form of weight $k$ over $R$ — a rule attaching to each $R$-algebra $A$, Weierstrass curve $W/A$ with unit discriminant and level-$p$ structure $D$ an element of $A$, compatible with $R$-algebra maps and scaling by $u^{-k}$ under variable change — which depends only on lines, i.e. is unchanged when each point is replaced by one whose $x$-coordinate is `InLine` with the old one, and which vanishes at $(T_R, D_R)$. Assume the analogous vanishing criterion over every field $K$ in the same universe with $p \neq 0$ in $K$: for each $\xi \in K^\times$ with $\sum_{i<p}\xi^i = 0$ such that `cuspData K p ξ ![0, 1] ![1, 1]` is a level-$p$ structure on `tateBase K p`, every weight-$k$ Katz level-$p$ form over $K$ depending only on lines and vanishing there is zero. Then $G = 0$.
--
--   This is the passage from field coefficients to arbitrary coefficient rings in which $p$ is invertible in the $q$-expansion principle for Katz modular forms with full level-$p$ structure depending only on the two lines. It is used by [`ModularCurve.KatzLevelPForm.eq_zero_of_dependsOnlyOnLines_of_forall_evalCusp_eq_zero`](thm.html#ModularCurve.KatzLevelPForm.eq_zero_of_dependsOnlyOnLines_of_forall_evalCusp_eq_zero), which combines it with the statement over fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnLines_of_evalCusp_eq_zero_of_forall_field.lean

import Mathlib
import Definitions.Def_ModularForm_KatzLevelOne
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPCusps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem ModularCurve.KatzLevelPForm.eq_zero_of_dependsOnlyOnLines_of_evalCusp_eq_zero_of_forall_field
    {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp : IsUnit (p : R))
    (ζ : Rˣ) (hζ : ∑ i ∈ Finset.range p, (ζ : R) ^ i = 0) {k : ℤ}
    (hc : ModularCurve.IsLevelPStructure (ModularCurve.tateBase R p) p
      (ModularCurve.cuspData R p ζ ![0, 1] ![1, 1]))
    (G : ModularCurve.KatzLevelPForm R p k) (hG : G.DependsOnlyOnLines)
    (h0 : G.toFun (ModularCurve.tateBase R p) (ModularCurve.isUnit_Δ_tateBase R p) _ hc = 0)
    (hF : ∀ (K : Type u) [Field K], (p : K) ≠ 0 → ∀ (ξ : Kˣ),
      ∑ i ∈ Finset.range p, (ξ : K) ^ i = 0 →
      ∀ (hcK : ModularCurve.IsLevelPStructure (ModularCurve.tateBase K p) p
        (ModularCurve.cuspData K p ξ ![0, 1] ![1, 1]))
      (H : ModularCurve.KatzLevelPForm K p k), H.DependsOnlyOnLines →
      H.toFun (ModularCurve.tateBase K p) (ModularCurve.isUnit_Δ_tateBase K p) _ hcK = 0 → H = 0) :
    G = 0 := by sorry
