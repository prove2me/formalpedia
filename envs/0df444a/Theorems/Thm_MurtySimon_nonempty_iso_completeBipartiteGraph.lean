-- Prove2me | Theorems.Thm_MurtySimon_nonempty_iso_completeBipartiteGraph
-- name    : MurtySimon.nonempty_iso_completeBipartiteGraph
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:21:13.919796+00:00
-- url     : https://prove2.me/theorems/512e8165-fec1-4179-86b7-4c23046a228c
-- title:
--   Murty Simon: nonempty iso complete Bipartite Graph
-- statement:
--   **Theorem 1.1**, the equality case: an `n`-vertex diameter-2-critical graph with `⌊n²/4⌋`
--   edges is isomorphic to `K_{⌈n/2⌉,⌊n/2⌋}`.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Main.lean#L195-L219
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Main.lean#L195-L219

module
public import Definitions.Def_MurtySimon_Equality
public import Definitions.Def_MurtySimon_Main
set_option autoImplicit true
@[expose] public section
public section
open MurtySimon
open Finset SimpleGraph
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}
variable [DecidableRel G.Adj]

theorem MurtySimon.nonempty_iso_completeBipartiteGraph (hG : IsDiameterTwoCritical G)
    (hE : #G.edgeFinset = Fintype.card V ^ 2 / 4) :
    Nonempty (G ≃g completeBipartiteGraph (Fin ((Fintype.card V + 1) / 2))
      (Fin (Fintype.card V / 2))) := by sorry
