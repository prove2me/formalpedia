-- Prove2me | Theorems.Thm_GalvinMultigraph_Gadget_terminal_proper
-- name    : GalvinMultigraph.Gadget.terminal_proper
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T01:19:38.998466+00:00
-- url     : https://prove2.me/theorems/fe2477c0-eaf2-47f1-b734-f603124b9be7
-- title:
--   Gadget: terminal proper
-- statement:
--   Terminal colors are proper at both original endpoints.
--
--   Source: https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Gadget.lean#L322-L336
-- source:
--   https://github.com/jtraverso/galvin-dinitz/blob/84dcda4c2a760f2b52b7e813affe7e6968f8bfce/GalvinMultigraph/Gadget.lean#L322-L336

module
public import Mathlib.Combinatorics.SimpleGraph.LineGraph
public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
public import Definitions.Def_GalvinMultigraph_Gadget
set_option autoImplicit true
@[expose] public section
public section
open GalvinMultigraph GalvinMultigraph.Gadget
open Finset SimpleGraph
variable {A B E Color : Type*} {k : ℕ} [NeZero k]

theorem GalvinMultigraph.Gadget.terminal_proper (a : E → A) (b : E → B)
    (col : (graph (k := k) a b).lineGraph.Coloring Color)
    (heq : ∀ e, col (aEdge a b e) = col (bEdge a b e)) :
    ∀ e f, e ≠ f → a e = a f ∨ b e = b f → col (aEdge a b e) ≠ col (aEdge a b f) := by sorry
