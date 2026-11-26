-- Prove2me | Theorems.Thm_MurtySimonConjecture_murty_simon_sharp
-- name    : MurtySimonConjecture.murty_simon_sharp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:21:59.003501+00:00
-- url     : https://prove2.me/theorems/65911886-3e89-4ecf-ad99-f7f21f12b812
-- title:
--   Murty Simon Conjecture: murty simon sharp
-- statement:
--   **Sharpness**: for `n ≥ 3`, `K_{⌈n/2⌉,⌊n/2⌋}` is diameter-2-critical and has `⌊n²/4⌋`
--   edges.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/Solution.lean#L80-L85
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/Solution.lean#L80-L85

module
public import Definitions.Def_MurtySimon_Main
public import Definitions.Def_MurtySimon_Solution
set_option autoImplicit true
@[expose] public section
public section
open MurtySimonConjecture
open Finset SimpleGraph
variable {V : Type*}

theorem MurtySimonConjecture.murty_simon_sharp (n : ℕ) (hn : 3 ≤ n) :
    IsDiameterTwoCritical (completeBipartiteGraph (Fin ((n + 1) / 2)) (Fin (n / 2))) ∧
      Nat.card (completeBipartiteGraph (Fin ((n + 1) / 2)) (Fin (n / 2))).edgeSet =
        n ^ 2 / 4 := by sorry
