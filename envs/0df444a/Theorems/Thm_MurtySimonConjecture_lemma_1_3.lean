-- Prove2me | Theorems.Thm_MurtySimonConjecture_lemma_1_3
-- name    : MurtySimonConjecture.lemma_1_3
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:25:48.389583+00:00
-- url     : https://prove2.me/theorems/e4b9bc51-88c0-40a8-99fd-f7bef1fea2d3
-- title:
--   Murty Simon Conjecture: lemma 1 3
-- statement:
--   **Lemma 1.3** (Das–Fox): a diameter-2-critical graph with `|E(G) \ M| = |non-edges of G|` for
--   every maximal matching `M` is triangle-free.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/Solution.lean#L96-L100
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/Solution.lean#L96-L100

module
public import Definitions.Def_MurtySimon_Main
public import Definitions.Def_MurtySimon_Solution
public import Theorems.Thm_MurtySimon_lemma_1_3

set_option autoImplicit true
@[expose] public section
public section
open MurtySimonConjecture
open Finset SimpleGraph
variable {V : Type*}

theorem MurtySimonConjecture.lemma_1_3 [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : IsDiameterTwoCritical G)
    (heq : ∀ M, IsMaximalEdgeMatching G M → #(G.edgeFinset \ M) = #Gᶜ.edgeFinset) :
    G.CliqueFree 3 := by sorry
