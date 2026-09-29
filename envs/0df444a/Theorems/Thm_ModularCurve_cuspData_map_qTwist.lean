-- Prove2me | Theorems.Thm_ModularCurve_cuspData_map_qTwist
-- name    : ModularCurve.cuspData_map_qTwist
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:49.889759+00:00
-- url     : https://prove2.me/theorems/3a125d30-2b23-56ce-a8bd-af849db3d54c
-- title:
--   q-twisting by ζ shifts level-p cusp data
-- statement:
--   Let $R$ be a commutative ring, $p$ a prime, $\zeta \in R^\times$ a unit with $\zeta^p = 1$, and let $v, w \colon \mathrm{Fin}\,2 \to \mathbb{Z}/p$ be two pairs of residues. Recall that [`ModularCurve.cuspPoint R p ζ v`](def/ModularCurve_KatzLevelPCusps.html#L59) is the pair of Laurent series over $R$ given by `tateToricPoint R p (ζ ^ (v 0).val)` when $v_1 = 0$ and by `nonToricPoint R p (ζ ^ (v 0).val) (v 1).val` otherwise, and that [`ModularCurve.cuspData R p ζ v w`](def/ModularCurve_KatzLevelPCusps.html#L71) is the `LevelPData` over $R((q))$ whose entries $x_P, y_P$ are the two components of `cuspPoint R p ζ v` and whose entries $x_Q, y_Q$ are the two components of `cuspPoint R p ζ w`. Let [`ModularCurve.qTwist ζ`](def/ModularCurve_PhiGen.html#L35) be the ring endomorphism of $R((q))$ multiplying the coefficient of index $k \in \mathbb{Z}$ by $\zeta^k$. The assertion is that applying `qTwist ζ` to all four entries of `cuspData R p ζ v w` yields exactly `cuspData R p ζ (cuspShift p v) (cuspShift p w)`, where `cuspShift p v = ![v 0 + v 1, v 1]`, i.e. $(a,b) \mapsto (a+b, b)$.
--
--   This records the effect of the substitution $q \mapsto \zeta q$ — the inertial action at a $p$-th root of unity — on the level-$p$ data attached to the cusps of the Tate curve $\mathrm{Tate}(q^p)$: the toric index $b$ is unchanged while the root-of-unity index $a$ is translated by $b$. It is used in the comparison of $q$-expansions at twisted cusps and in the vanishing criterion for Katz level-$p$ forms over a field that depend only on lines.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_cuspData_map_qTwist.lean

import Mathlib
import Definitions.Def_ModularForm_KatzLevelOne
import Definitions.Def_ModularCurve_KatzLevelP
import Definitions.Def_ModularCurve_KatzLevelPCusps

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

theorem ModularCurve.cuspData_map_qTwist {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime]
    (ζ : Rˣ) (hζ : ζ ^ p = 1) (v w : Fin 2 → ZMod p) :
    (ModularCurve.cuspData R p ζ v w).map (ModularCurve.qTwist ζ)
      = ModularCurve.cuspData R p ζ (ModularCurve.cuspShift p v) (ModularCurve.cuspShift p w) := by sorry
