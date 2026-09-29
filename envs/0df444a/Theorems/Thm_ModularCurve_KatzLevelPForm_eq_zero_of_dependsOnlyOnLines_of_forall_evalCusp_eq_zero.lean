-- Prove2me | Theorems.Thm_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnLines_of_forall_evalCusp_eq_zero
-- name    : ModularCurve.KatzLevelPForm.eq_zero_of_dependsOnlyOnLines_of_forall_evalCusp_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/b3373b92-18f6-5a78-b4fa-7441ed25c776
-- title:
--   q-expansion principle at split Cartan level p
-- statement:
--   Let $p$ be an odd prime, let $R_0$ be a commutative ring in which $p$ is a unit, and let $R$ be a commutative $R_0$-algebra (in the same universe) that is faithfully flat as an $R_0$-module. Let $\zeta \in R^{\times}$ satisfy $\sum_{i<p}\zeta^{i}=0$, and let $k \in \mathbb{Z}$. Assume that for every pair $v,w : \mathbb{Z}/p \to$ (indexed by `Fin 2`) with $v_0w_1-v_1w_0 \neq 0$ the data `cuspData R p ζ v w`, whose two points are the toric point attached to $\zeta^{v_0}$ when $v_1=0$ and the non-toric point attached to $\zeta^{v_0}$ and $v_1$ otherwise, is a level-$p$ structure on the Tate curve `tateBase R p` over `LaurentSeries R`: both points satisfy the affine Weierstrass equation, both $x$-coordinates are roots of $\mathrm{pre}\Psi_p$, and both products $\prod_{a=1}^{(p-1)/2}\bigl(x\,\Psi^2_a(x_0)-\Phi_a(x_0)\bigr)$ are units. Let $G$ be a Katz level-$p$ form of weight $k$ over $R_0$, that is, a rule assigning to every $R_0$-algebra $A$, every Weierstrass curve $W/A$ with unit discriminant and every level-$p$ structure $D$ on $W$ an element of $A$, compatible with $R_0$-algebra maps and scaling by $u^{-k}$ under variable change. Assume $G$ depends only on lines: its values at two level-$p$ structures on the same $W$ agree whenever the $x$-coordinates of the first points, and those of the second points, are related by `InLine`, i.e. $x\,\Psi^2_a(x_0)=\Phi_a(x_0)$ for some $1 \le a \le (p-1)/2$. If $G$ vanishes at `cuspData R p ζ v w` for all $v,w$ with $v_0w_1-v_1w_0 \neq 0$, $v_1 \neq 0$ and $w_1 \neq 0$, then $G = 0$.
--
--   This is the $q$-expansion principle for the moduli problem of a curve together with an unordered-free pair of lines of order $p$ (the split Cartan problem): vanishing of a line-dependent Katz level-$p$ form at the cusps where both lines are non-toric forces the form to vanish identically. It feeds the comparison of $\Gamma_0$-forms with their pullbacks to level $p$ in [`ModularCurve.KatzGamma0Form.exists_pullbackLevelP_eq_of_qTwist_qExpansion_eq_of_five_le`](thm.html#ModularCurve.KatzGamma0Form.exists_pullbackLevelP_eq_of_qTwist_qExpansion_eq_of_five_le), and is reduced, by faithful flatness, to the corresponding statements over fields.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_KatzLevelPForm_eq_zero_of_dependsOnlyOnLines_of_forall_evalCusp_eq_zero.lean

import Mathlib
import Definitions.Def_ModularForm_KatzLevelOne
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPCusps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem ModularCurve.KatzLevelPForm.eq_zero_of_dependsOnlyOnLines_of_forall_evalCusp_eq_zero
    {R₀ : Type u} [CommRing R₀] {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hp : IsUnit (p : R₀))
    (R : Type u) [CommRing R] [Algebra R₀ R] [Module.FaithfullyFlat R₀ R]
    (ζ : Rˣ) (hζ : ∑ i ∈ Finset.range p, (ζ : R) ^ i = 0) {k : ℤ}
    (hc : ∀ v w : Fin 2 → ZMod p, v 0 * w 1 - v 1 * w 0 ≠ 0 →
      ModularCurve.IsLevelPStructure (ModularCurve.tateBase R p) p (ModularCurve.cuspData R p ζ v w))
    (G : ModularCurve.KatzLevelPForm R₀ p k) (hG : G.DependsOnlyOnLines)
    (h0 : ∀ (v w : Fin 2 → ZMod p) (hvw : v 0 * w 1 - v 1 * w 0 ≠ 0), v 1 ≠ 0 → w 1 ≠ 0 →
      G.toFun (ModularCurve.tateBase R p) (ModularCurve.isUnit_Δ_tateBase R p) _ (hc v w hvw) = 0) : G = 0 := by sorry
