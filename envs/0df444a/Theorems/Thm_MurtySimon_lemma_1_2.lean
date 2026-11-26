-- Prove2me | Theorems.Thm_MurtySimon_lemma_1_2
-- name    : MurtySimon.lemma_1_2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:20:11.603166+00:00
-- url     : https://prove2.me/theorems/7f89569e-7f16-58ab-99c1-3903b1fc14d1
-- title:
--   Murty Simon: lemma 1 2
-- statement:
--   **Lemma 1.2.** For a diameter-2-critical graph and a maximal matching `M`,
--   `|E(G) \ M| ≤ |non-edges of G|`.
--
--   Source: https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Main.lean#L127-L130
-- source:
--   https://github.com/jtraverso/murty-simon-conjecture/blob/adadd2fbd0ba9e9c71faadd105f357f7b12a814f/MurtySimon/Main.lean#L127-L130

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

theorem MurtySimon.lemma_1_2 (hG : IsDiameterTwoCritical G) {M : Finset (Sym2 V)}
    (hM : IsMaximalEdgeMatching G M) : #(G.edgeFinset \ M) ≤ #Gᶜ.edgeFinset := by sorry
