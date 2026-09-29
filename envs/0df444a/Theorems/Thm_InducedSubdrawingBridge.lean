-- Prove2me | Theorems.Thm_InducedSubdrawingBridge
-- name    : InducedSubdrawingBridge
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-26T20:44:34.547061+00:00
-- url     : https://prove2.me/theorems/46d99452-8759-4e8a-b4ad-dc2a89ff12a6
-- title:
--   Induced-subgraph drawing bridge
-- statement:
--   Given an ordinary polygonal drawing $D$ of a finite simple graph $G$ and a vertex subset $S$, one can draw the induced graph $G[S]$ by restricting the vertex placement and retaining exactly the edges whose endpoints lie in $S$.
--
--   The bridge identifies every induced edge with its original edge, characterizes the induced crossing set by crossings of retained original edges, and shows that a drawing with no adjacent-edge crossings has no common endpoint between any two edges crossing in their relative interiors. These correspondences let crossing-number inequalities for induced subgraphs be compared with the original drawing.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/InducedSubdrawingBridge.lean#L1-L228

import Definitions.Def_OrdinaryPolygonalDrawing
import Mathlib.Combinatorics.SimpleGraph.Copy

set_option maxHeartbeats 1000000

open Classical
noncomputable section

lemma InducedSubdrawingBridge {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] (D : OrdinaryPolygonalDrawing G) (S : Set V)
    [Fintype S] [Fintype (G.induce S).edgeSet] :
    ∃ DX : OrdinaryPolygonalDrawing (G.induce S),
      DX.vertexPlacement = (fun v : S => D.vertexPlacement v.1) ∧
        (∀ ed : (G.induce S).edgeFinset,
          ∃ eG : G.edgeFinset,
            eG.1 = Sym2.map (Subtype.val : S → V) ed.1 ∧
              (∀ v : V, v ∈ eG.1 → v ∈ S) ∧
              DX.edgeArc ed = D.edgeArc eG) ∧
        (∀ p : EuclideanSpace ℝ (Fin 2),
          p ∈ DX.crossingSet ↔
            ∃ e₁ e₂ : G.edgeFinset,
              e₁ ≠ e₂ ∧
                (∀ v : V, v ∈ e₁.1 → v ∈ S) ∧
                  (∀ v : V, v ∈ e₂.1 → v ∈ S) ∧
                    p ∈ (D.edgeArc e₁).relativeInterior ∧
                      p ∈ (D.edgeArc e₂).relativeInterior) ∧
          (D.adjacentEdgeCrossingCount = 0 →
            ∀ ⦃p : EuclideanSpace ℝ (Fin 2)⦄ ⦃e₁ e₂ : G.edgeFinset⦄,
              e₁ ≠ e₂ →
                p ∈ (D.edgeArc e₁).relativeInterior →
                  p ∈ (D.edgeArc e₂).relativeInterior →
                    ¬ ∃ v : V, v ∈ e₁.1 ∧ v ∈ e₂.1) := by sorry
