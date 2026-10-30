-- Prove2me | Theorems.Thm_OPG1808_order_eight_normalized_cycle_prefix0011
-- name    : OPG1808.order_eight_normalized_cycle_prefix0011
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-30T03:04:18.380428+00:00
-- url     : https://prove2.me/theorems/f1418fc0-2d0e-44a0-82b8-c24735cbb0d9
-- title:
--   Eight-vertex normalized cycles with leading colors 0011
-- statement:
--   Consider a three-colored tournament on vertices $0,\ldots,7$ with no directed rainbow triangle and with the directed forward cycle $i\to i+1\pmod8$. Assume its forward-edge color word is lexicographically least under cyclic rotation and color permutation. If its leading colors are $0011$, then some successor reaches its cycle predecessor by a monochromatic directed path.
--
--   The path may use all eight vertices. The cases $0010$, $0011$, and $0012$ exhaust the possible next colors after the leading pattern $001$. They discharge the remaining case in the canonical bound through eight, a supporting finite theorem for the existing order-eleven target. This is a finite supporting formalization, without a claim of a new mathematical discovery.
-- source:
--   Finite supporting subcase of OPG1808.order_eight_to_eleven_cycle_predecessor_reachable, https://prove2.me/theorems/0e61f60b-2fb6-4669-a700-21d27396b433. Uses the accepted order-seven theorem to justify confined interval paths and ordinary Lean LRAT reconstruction for the finite case. These are supporting formalizations, not new mathematical discoveries.

import Definitions.Def_opg1808_colored_tournaments
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Order.PiLex

open OPG1808

theorem OPG1808.order_eight_normalized_cycle_prefix0011
    (D : Digraph (Fin 8)) (color : ArcColoring (Fin 8))
    (htournament : IsTournament D)
    (hnoRainbow : ¬HasRainbowDirectedTriangle D color)
    (hcycle : ∀ i : Fin 8, D i (finRotate 8 i))
    (hminimal : ∀ r : Fin 8, ∀ σ : Equiv.Perm (Fin 3),
      toLex (fun i ↦ color i (finRotate 8 i)) ≤
        toLex (fun i ↦ σ (color (i + r) (finRotate 8 (i + r)))))
    (hprefix0 : color (0:Fin 8) (finRotate 8 (0:Fin 8)) = (0:Fin 3))
    (hprefix1 : color (1:Fin 8) (finRotate 8 (1:Fin 8)) = (0:Fin 3))
    (hprefix2 : color (2:Fin 8) (finRotate 8 (2:Fin 8)) = (1:Fin 3))
    (hprefix3 : color (3:Fin 8) (finRotate 8 (3:Fin 8)) = (1:Fin 3)) :
    ∃ i : Fin 8, MonochromaticallyReaches D color (finRotate 8 i) i := by sorry
