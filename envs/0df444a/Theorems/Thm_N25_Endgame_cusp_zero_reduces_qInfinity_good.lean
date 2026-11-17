-- Prove2me | Theorems.Thm_N25_Endgame_cusp_zero_reduces_qInfinity_good
-- name    : N25.Endgame.cusp_zero_reduces_qInfinity_good
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:57:16.504452+00:00
-- url     : https://prove2.me/theorems/24443cce-209a-414d-88b3-b2a18c9b6a28
-- title:
--   The first selected cusp reduces to the $q$-infinity place
-- statement:
--   Let $p$ be prime with $p=2$ or $p=3$, let $D$ be a level-$25$ reduction datum at $p$, let $p_0$ be the first selected geometric cusp, and let $q_∞$ be the canonical infinity place of the special function field over the residue field $κ(D.A)$. Then
--
--   $$red_D(p_0)=q_∞.$$
--
--   This identifies one specialized cusp with the standard $q$-expansion place.
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

theorem N25.Endgame.cusp_zero_reduces_qInfinity_good
    (p : ℕ) [Fact p.Prime] (hp : p = 2 ∨ p = 3) (D : RedDatum25 p) :
    redPlace25 D (pG25 0) =
      ModularCurve.qInftyPlaceMod (κ D.A) (jBase25 (κ D.A)).property := by sorry
