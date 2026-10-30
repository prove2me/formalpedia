-- Prove2me | Theorems.Thm_OPG1808_order_eight_normalized_cycle_prefix001
-- name    : OPG1808.order_eight_normalized_cycle_prefix001
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-10-30T02:28:01.714446+00:00
-- url     : https://prove2.me/theorems/e63d9792-601d-47fe-8fd6-8f3b490f5a1c
-- title:
--   Eight-vertex normalized cycles with leading colors 001
-- statement:
--   Let the arcs of a tournament on the eight vertices $0,\ldots,7$ have three colors, and suppose there is no directed rainbow triangle. Assume the forward edges $i\to i+1\pmod8$ form a directed cycle. Normalize its forward-edge color word to be lexicographically least under all rotations and all permutations of the three colors. If its leading colors are $001$, then some cycle successor reaches its predecessor by a monochromatic directed path.
--
--   The path may use any of the eight vertices. Together, the leading-color cases $000$, $001$, and $01$ cover every normalized word. These three physical subcases support the canonical bound through eight, and thereby the existing order-eleven formalization target. This is a known finite supporting formalization, without a claim of a new mathematical discovery.
-- source:
--   Finite supporting subcase of OPG1808.order_eight_to_eleven_cycle_predecessor_reachable, https://prove2.me/theorems/0e61f60b-2fb6-4669-a700-21d27396b433. Uses the accepted order-seven theorem to justify confined interval paths and ordinary Lean LRAT reconstruction for the finite case. These are supporting formalizations, not new mathematical discoveries.

import Definitions.Def_opg1808_colored_tournaments
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Order.PiLex

open OPG1808

theorem OPG1808.order_eight_normalized_cycle_prefix001
    (D : Digraph (Fin 8)) (color : ArcColoring (Fin 8))
    (htournament : IsTournament D)
    (hnoRainbow : ¬HasRainbowDirectedTriangle D color)
    (hcycle : ∀ i : Fin 8, D i (finRotate 8 i))
    (hminimal : ∀ r : Fin 8, ∀ σ : Equiv.Perm (Fin 3),
      toLex (fun i ↦ color i (finRotate 8 i)) ≤
        toLex (fun i ↦ σ (color (i + r) (finRotate 8 (i + r)))))
    (hprefix0 : color (0:Fin 8) (finRotate 8 (0:Fin 8)) = (0:Fin 3))
    (hprefix1 : color (1:Fin 8) (finRotate 8 (1:Fin 8)) = (0:Fin 3))
    (hprefix2 : color (2:Fin 8) (finRotate 8 (2:Fin 8)) = (1:Fin 3)) :
    ∃ i : Fin 8, MonochromaticallyReaches D color (finRotate 8 i) i := by sorry
