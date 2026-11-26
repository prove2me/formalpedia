-- Prove2me | Theorems.Thm_MurtySimon_lemma_1_3
-- name    : MurtySimon.lemma_1_3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:20:11.222938+00:00
-- url     : https://prove2.me/theorems/93e18d68-559a-521d-91b6-91de04cd1a7f
-- title:
--   Murty Simon: lemma 1 3
-- statement:
--   **Lemma 1.3.** A diameter-2-critical graph with equality in Lemma 1.2 for every maximal
--   matching is triangle-free.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Main.lean#L134-L139
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Main.lean#L134-L139

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

theorem MurtySimon.lemma_1_3 (hG : IsDiameterTwoCritical G)
    (heq : ∀ M, IsMaximalEdgeMatching G M → #(G.edgeFinset \ M) = #Gᶜ.edgeFinset) :
    G.CliqueFree 3 := by sorry
