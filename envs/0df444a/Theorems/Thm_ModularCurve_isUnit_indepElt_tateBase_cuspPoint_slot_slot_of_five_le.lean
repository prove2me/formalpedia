-- Prove2me | Theorems.Thm_ModularCurve_isUnit_indepElt_tateBase_cuspPoint_slot_slot_of_five_le
-- name    : ModularCurve.isUnit_indepElt_tateBase_cuspPoint_slot_slot_of_five_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:53.34379+00:00
-- url     : https://prove2.me/theorems/75a1fed9-6546-5d8a-a413-d85605ca20b2
-- title:
--   Unit independence element at two non-toric cusp slots
-- statement:
--   Let $R$ be a commutative ring, $p$ a prime with $p \ge 5$ whose image in $R$ is a unit, and $\zeta \in R^{\times}$ a unit satisfying $\sum_{i<p} \zeta^{i} = 0$. Let $v, w \colon \mathrm{Fin}\,2 \to \mathbb{Z}/p$ be two vectors with $v_1 \neq 0$, $w_1 \neq 0$ and $v_0 w_1 - v_1 w_0 \neq 0$, so that $v$ and $w$ span distinct lines and neither is toric. Work on the Weierstrass curve [`ModularCurve.tateBase R p`](def/ModularCurve_TateSlots.html#L46), the formal Tate curve over the Laurent series ring $R((q))$ pulled back along the substitution $q \mapsto q^{p}$ (the $q$-expansion map multiplying exponents by $p$). Write $x_P$ and $x_Q$ for the first coordinates of [`ModularCurve.cuspPoint R p ζ v`](def/ModularCurve_KatzLevelPCusps.html#L59) and [`ModularCurve.cuspPoint R p ζ w`](def/ModularCurve_KatzLevelPCusps.html#L59); since $v_1, w_1 \neq 0$, each is the $x$-coordinate of the non-toric slot point attached to the unit $\zeta^{(v_0).\mathrm{val}}$ (resp. $\zeta^{(w_0).\mathrm{val}}$) and the index $(v_1).\mathrm{val}$ (resp. $(w_1).\mathrm{val}$), obtained from the universal Tate $x$-series by the slot substitution. The assertion is that the independence element
--   $$\prod_{e=1}^{(p-1)/2}\bigl(x_Q\,\Psi^{2}_{e}(x_P) - \Phi_{e}(x_P)\bigr),$$
--   formed from the division-polynomial data $\Psi^{2}_{e}$, $\Phi_{e}$ of [`ModularCurve.tateBase R p`](def/ModularCurve_TateSlots.html#L46) evaluated at $x_P$, is a unit of $R((q))$.
--
--   This is the case of two non-toric cusp slots in the verification that the level-$p$ independence element does not vanish at the cusps of the Tate curve: it expresses that the two cusp points, lying on distinct lines of $(\mathbb{Z}/p)^2$, generate independent points of order $p$. It is used by [`ModularCurve.isUnit_indepElt_tateBase_cuspPoint_of_five_le`](thm.html#ModularCurve.isUnit_indepElt_tateBase_cuspPoint_of_five_le), which combines it with the mixed toric/non-toric cases.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_isUnit_indepElt_tateBase_cuspPoint_slot_slot_of_five_le.lean

import Mathlib
import Definitions.Def_ModularForm_KatzLevelOne
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPCusps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem ModularCurve.isUnit_indepElt_tateBase_cuspPoint_slot_slot_of_five_le {R : Type u} [CommRing R]
    {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (hp : IsUnit (p : R)) (ζ : Rˣ)
    (hζ : ∑ i ∈ Finset.range p, (ζ : R) ^ i = 0) (v w : Fin 2 → ZMod p)
    (hv : v 1 ≠ 0) (hw : w 1 ≠ 0) (hvw : v 0 * w 1 - v 1 * w 0 ≠ 0) :
    IsUnit (ModularCurve.indepElt (ModularCurve.tateBase R p) p
      (ModularCurve.cuspPoint R p ζ v).1 (ModularCurve.cuspPoint R p ζ w).1) := by sorry
