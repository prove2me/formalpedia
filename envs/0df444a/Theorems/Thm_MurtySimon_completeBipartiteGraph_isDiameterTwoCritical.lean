-- Prove2me | Theorems.Thm_MurtySimon_completeBipartiteGraph_isDiameterTwoCritical
-- name    : MurtySimon.completeBipartiteGraph_isDiameterTwoCritical
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:21:25.010019+00:00
-- url     : https://prove2.me/theorems/c5090c30-6429-48d7-8edc-1578bd6d7436
-- title:
--   Murty Simon: complete Bipartite Graph is Diameter Two Critical
-- statement:
--   For `n ≥ 3`, `K_{⌈n/2⌉,⌊n/2⌋}` is diameter-2-critical.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Main.lean#L241-L263
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Main.lean#L241-L263

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

theorem MurtySimon.completeBipartiteGraph_isDiameterTwoCritical {n : ℕ} (hn : 3 ≤ n) :
    IsDiameterTwoCritical (completeBipartiteGraph (Fin ((n + 1) / 2)) (Fin (n / 2))) := by sorry
