-- Prove2me | Theorems.Thm_N25_Endgame_cusp_zero_reduction_fixed_good
-- name    : N25.Endgame.cusp_zero_reduction_fixed_good
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:57:22.022859+00:00
-- url     : https://prove2.me/theorems/4dcefef1-6a97-4c4e-ad33-cc1ffdc04866
-- title:
--   The reduction of the first cusp is Frobenius fixed
-- statement:
--   Let $p$ be prime with $p=2$ or $p=3$, let $D$ be a level-$25$ reduction datum at $p$, let $p_0$ be the first selected geometric cusp, and let $Fr_D$ act on special-fiber places. Then
--
--   $$Fr_D(red_D(p_0))=red_D(p_0).$$
--
--   This supplies a distinguished Frobenius-fixed place in both good characteristics.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_CuspReduction
import Definitions.Def_N25_SelectedCusps
import Definitions.Def_N25_Units
import Definitions.Def_N25_UnitOrders
import Definitions.Def_N25_UnitSeries

set_option autoImplicit false
open N25
open N25.Endgame

theorem N25.Endgame.cusp_zero_reduction_fixed_good
    (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3) (D : RedDatum25 p) :
    frobPlace25 D (redPlace25 D (pG25 0)) = redPlace25 D (pG25 0) := by sorry
