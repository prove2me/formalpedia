-- Prove2me | Theorems.Thm_Konig_exists_total_of_bipartite
-- name    : Konig.exists_total_of_bipartite
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:12:12.307202+00:00
-- url     : https://prove2.me/theorems/faa36680-2c29-4746-8e2f-9539df51b5bc
-- title:
--   Konig: exists total of bipartite
-- statement:
--   **Kőnig's theorem.** A finite bipartite graph has a total proper partial edge colouring with
--   any colour type of size at least `Δ(G)`.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/Konig/Basic.lean#L168-L205
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/Konig/Basic.lean#L168-L205

module
public import Definitions.Def_LeanPool_Vizing_Main
public import Definitions.Def_Konig_Basic
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open Konig
open LeanPool.Vizing LeanPool.Vizing.PEC
variable {V : Type*} {C : Type*} {G : SimpleGraph V}

theorem Konig.exists_total_of_bipartite [Fintype V] [Fintype C] [DecidableRel G.Adj]
    (s : G.Coloring (Fin 2))
    (hcard : G.maxDegree ≤ Fintype.card C) :
    ∃ c : PEC G C, ∀ u v, G.Adj u v → c.col u v ≠ none := by sorry
