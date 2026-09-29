-- Prove2me | Theorems.Thm_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero_of_forall_field
-- name    : ModularCurve.KatzLevelPForm.eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero_of_forall_field
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/c869bf75-a508-5df4-a7d6-3de9c2e21731
-- title:
--   Descent of the q-expansion principle from fields
-- statement:
--   Let $R$ be a commutative ring, let $p$ be a prime with $p \neq 2$ whose image in $R$ is a unit, let $\zeta \in R^\times$ satisfy $\sum_{i<p}\zeta^{i}=0$, and let $k \in \mathbb{Z}$. Here `tateBase R p` is the Tate Weierstrass curve over the Laurent series $R((q))$ transported along `qExpand R p`, the ring map multiplying $q$-exponents by $p$, and `cuspData R p ζ ![1,0] ![0,1]` is the level-$p$ datum whose first point is `tateToricPoint R p (ζ ^ 1)` and whose second point is `nonToricPoint R p (ζ ^ 0) 1`. It is assumed that this datum is a level-$p$ structure on `tateBase R p`, i.e. both points satisfy the affine Weierstrass equation, `preΨ p` vanishes at both $x$-coordinates, and both independence elements `indepElt` (in either order) are units. Let $G$ be a Katz level-$p$ form of weight $k$ over $R$: a rule attaching to every $R$-algebra $A$ in the universe of $R$, every Weierstrass curve $W/A$ with invertible discriminant and every level-$p$ structure $D$ on $W$ an element of $A$, compatible with $R$-algebra maps and multiplied by $u^{-k}$ under a variable change with scaling unit $u$. Assume $G$ depends only on the second line, meaning that if $D,D'$ are level-$p$ structures on one and the same $W$ and $x_{Q'}\cdot(\Psi_a^{2})(x_{Q}) = \Phi_a(x_{Q})$ for some $1 \le a \le (p-1)/2$, then $G$ takes the same value at $D$ and at $D'$. Assume further that $G$ vanishes at the above cusp datum on `tateBase R p`, and that the analogous vanishing statement holds over all fields: for every field $K$ in the universe of $R$ with $p \neq 0$ in $K$, every $\xi \in K^\times$ such that `cuspData K p ξ ![1,0] ![0,1]` is a level-$p$ structure on `tateBase K p`, and every Katz level-$p$ form $H$ of weight $k$ over $K$ depending only on the second line, vanishing of $H$ at that cusp datum forces $H = 0$. Then $G = 0$.
--
--   This is the passage from field coefficients to general coefficients in the $q$-expansion principle for forms of level $p$ depending only on the second line: vanishing at the Tate cusp datum over $R$ implies vanishing of the form, granted the same implication over all fields. It feeds into [`ModularCurve.KatzLevelPForm.eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero`](thm.html#ModularCurve.KatzLevelPForm.eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero), where the hypothesis over fields is discharged.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero_of_forall_field.lean

import Mathlib
import Definitions.Def_ModularForm_KatzLevelOne
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPCusps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem ModularCurve.KatzLevelPForm.eq_zero_of_dependsOnlyOnSndLine_of_evalCusp_eq_zero_of_forall_field
    {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp : IsUnit (p : R))
    (ζ : Rˣ) (hζ : ∑ i ∈ Finset.range p, (ζ : R) ^ i = 0) {k : ℤ}
    (hc : ModularCurve.IsLevelPStructure (ModularCurve.tateBase R p) p
      (ModularCurve.cuspData R p ζ ![1, 0] ![0, 1]))
    (G : ModularCurve.KatzLevelPForm R p k) (hG : G.DependsOnlyOnSndLine)
    (h0 : G.toFun (ModularCurve.tateBase R p) (ModularCurve.isUnit_Δ_tateBase R p) _ hc = 0)
    (hF : ∀ (K : Type u) [Field K], (p : K) ≠ 0 → ∀ (ξ : Kˣ)
      (hcK : ModularCurve.IsLevelPStructure (ModularCurve.tateBase K p) p
        (ModularCurve.cuspData K p ξ ![1, 0] ![0, 1]))
      (H : ModularCurve.KatzLevelPForm K p k), H.DependsOnlyOnSndLine →
      H.toFun (ModularCurve.tateBase K p) (ModularCurve.isUnit_Δ_tateBase K p) _ hcK = 0 → H = 0) :
    G = 0 := by sorry
