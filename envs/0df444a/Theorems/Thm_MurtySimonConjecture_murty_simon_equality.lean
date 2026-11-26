-- Prove2me | Theorems.Thm_MurtySimonConjecture_murty_simon_equality
-- name    : MurtySimonConjecture.murty_simon_equality
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:21:44.484804+00:00
-- url     : https://prove2.me/theorems/e43a1cf2-937a-5f42-bd11-237335c97545
-- title:
--   Murty Simon Conjecture: murty simon equality
-- statement:
--   **The equality case** (Das–Fox, Theorem 1.1): a diameter-2-critical graph on `n` vertices
--   with `⌊n²/4⌋` edges is isomorphic to `K_{⌈n/2⌉,⌊n/2⌋}`.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/Solution.lean#L71-L76
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/Solution.lean#L71-L76

module
public import Definitions.Def_MurtySimon_Main
public import Definitions.Def_MurtySimon_Solution
set_option autoImplicit true
@[expose] public section
public section
open MurtySimonConjecture
open Finset SimpleGraph
variable {V : Type*}

theorem MurtySimonConjecture.murty_simon_equality [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hG : IsDiameterTwoCritical G)
    (hE : #G.edgeFinset = Fintype.card V ^ 2 / 4) :
    Nonempty (G ≃g completeBipartiteGraph (Fin ((Fintype.card V + 1) / 2))
      (Fin (Fintype.card V / 2))) := by sorry
