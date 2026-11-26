-- Prove2me | Theorems.Thm_MurtySimonConjecture_lemma_1_2
-- name    : MurtySimonConjecture.lemma_1_2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:25:44.866884+00:00
-- url     : https://prove2.me/theorems/6558ee89-2918-5bca-843a-a98dcef58d4d
-- title:
--   Murty Simon Conjecture: lemma 1 2
-- statement:
--   **Lemma 1.2** (Das–Fox): for every maximal matching `M` of a diameter-2-critical graph,
--   `|E(G) \ M| ≤ |non-edges of G|`.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/Solution.lean#L89-L92
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/Solution.lean#L89-L92

module
public import Definitions.Def_MurtySimon_Main
public import Definitions.Def_MurtySimon_Solution
public import Theorems.Thm_MurtySimon_lemma_1_2

set_option autoImplicit true
@[expose] public section
public section
open MurtySimonConjecture
open Finset SimpleGraph
variable {V : Type*}

theorem MurtySimonConjecture.lemma_1_2 [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : IsDiameterTwoCritical G) (M : Finset (Sym2 V)) (hM : IsMaximalEdgeMatching G M) :
    #(G.edgeFinset \ M) ≤ #Gᶜ.edgeFinset := by sorry
