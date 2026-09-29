-- Prove2me | Theorems.Thm_ModularCurve_isUnit_indepElt_tateBase_cuspPoint_of_five_le
-- name    : ModularCurve.isUnit_indepElt_tateBase_cuspPoint_of_five_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/0b92ac57-568d-541b-9b86-11708b5cce87
-- title:
--   Unit independence element for two p-torsion cusp points
-- statement:
--   Let $R$ be a commutative ring and $p$ a prime with $5 \le p$, and assume that $p$ is a unit in $R$. Let $\zeta$ be a unit of $R$ whose image satisfies $\sum_{i<p} \zeta^{i} = 0$, and let $v, w : \mathbb{Z}/p \to \mathbb{Z}/p$ be two vectors indexed by $\mathrm{Fin}\,2$, i.e. pairs $(v_0,v_1)$, $(w_0,w_1)$ in $(\mathbb{Z}/p)^2$, subject to the single hypothesis $v_0 w_1 - v_1 w_0 \ne 0$ in $\mathbb{Z}/p$. Write $W =$ [`ModularCurve.tateBase R p`](def/ModularCurve_TateSlots.html#L46) for the Tate Weierstrass curve over the Laurent series ring $R((q))$, obtained from the universal Tate curve over $\mathbb{Z}[[q]]$ by base change to $R((q))$ followed by the substitution $q \mapsto q^{p}$. For a vector $u$, the point [`ModularCurve.cuspPoint R p ζ u`](def/ModularCurve_KatzLevelPCusps.html#L59) is, by definition, the toric point `tateToricPoint R p (ζ^(u 0).val)` when $u_1 = 0$, and otherwise the $u_1$-th slot point `nonToricPoint R p (ζ^(u 0).val) (u 1).val`, both given by explicit power series expansions; let $x_P$ and $x_Q$ be the first (abscissa) components attached to $v$ and $w$. The conclusion is that the independence element $$\prod_{a=1}^{(p-1)/2}\bigl(x_Q\,(W.\Psi\mathrm{Sq}\;a)(x_P) - (W.\Phi\;a)(x_P)\bigr)$$ is a unit of $R((q))$.
--
--   The element expresses that the two cusp points, thought of as the points $\zeta^{a}q^{b}$ and $\zeta^{c}q^{d}$ of the Tate curve $\mathrm{Tate}(q^{p})$ with $ad-bc \ne 0$, generate a full level-$p$ structure: no nonzero multiple $a\cdot P$ with $1 \le a \le (p-1)/2$ has the same abscissa as $Q$. It is used in the verification that the cusp data define a level-$p$ structure on the Tate curve, via [`ModularCurve.isLevelPStructure_cuspData`](thm.html#ModularCurve.isLevelPStructure_cuspData).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isUnit_indepElt_tateBase_cuspPoint_of_five_le.lean

import Mathlib
import Definitions.Def_ModularForm_KatzLevelOne
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPCusps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem ModularCurve.isUnit_indepElt_tateBase_cuspPoint_of_five_le {R : Type u} [CommRing R] {p : ℕ}
    [Fact p.Prime] (hp5 : 5 ≤ p) (hp : IsUnit (p : R)) (ζ : Rˣ)
    (hζ : ∑ i ∈ Finset.range p, (ζ : R) ^ i = 0) (v w : Fin 2 → ZMod p)
    (hvw : v 0 * w 1 - v 1 * w 0 ≠ 0) :
    IsUnit (ModularCurve.indepElt (ModularCurve.tateBase R p) p
      (ModularCurve.cuspPoint R p ζ v).1 (ModularCurve.cuspPoint R p ζ w).1) := by sorry
