-- Prove2me | Theorems.Thm_NoAdjacentMinimalDrawing
-- name    : NoAdjacentMinimalDrawing
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-26T20:44:37.038784+00:00
-- url     : https://prove2.me/theorems/5cea3062-1619-42a4-81cf-d75f9c555e17
-- title:
--   Minimal drawing without adjacent crossings
-- statement:
--   Every finite simple graph has an ordinary polygonal drawing that realizes the graph crossing number and has no crossing between adjacent edges:
--
--   $$
--   \exists D,\quad |\operatorname{crossingSet}(D)|=\operatorname{CrossingNumber}(G)
--   \quad\text{and}\quad
--   \operatorname{adjacentEdgeCrossingCount}(D)=0.
--   $$
--
--   The statement is obtained by choosing a crossing-minimal drawing and locally rerouting the tails of any pair of adjacent crossing edges. It is the general-position drawing used by the crossing-lemma proof.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/NoAdjacentMinimalDrawing.lean#L1-L38

import Definitions.Def_CrossingNumber

open Classical
noncomputable section

lemma NoAdjacentMinimalDrawing {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] :
    ∃ D : OrdinaryPolygonalDrawing G,
      D.crossingSet.card = CrossingNumber G ∧ D.adjacentEdgeCrossingCount = 0 := by sorry
