-- Prove2me | Theorems.Thm_OAI_CriticalZ3_LatticeGraph_bondConn_iff_hypergraph
-- name    : OAI.CriticalZ3.LatticeGraph.bondConn_iff_hypergraph
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:11:25.465102+00:00
-- url     : https://prove2.me/theorems/dc3886c5-f9cf-4e4a-bb9b-098ae38ca195
-- title:
--   Bond connectivity equals hypergraph connectivity
-- statement:
--   A finite lattice graph $G$ is a finite set of vertices of $\mathbb Z^3$ with finitely many bonds between them; bond percolation on $G$ uses the product law on its bonds. Each bond defines the two-element hyperedge of its endpoints. For every bond configuration $\omega$ and vertices $x,y$ of $G$,
--   $$
--   x\leftrightarrow y\ \text{by open bonds of }G\iff x\leftrightarrow y\ \text{in the bond hypergraph}.
--   $$
--
--   So bond percolation on $G$ is a special case of hypergraph percolation.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/LatticeGraph.lean#L118-L142

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
import Definitions.Def_OAI_Probability_CriticalZ3_LatticeGraph

open OAI OAI.CriticalZ3 OAI.CriticalZ3.LatticeGraph
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open Classical MeasureTheory ProbabilityTheory
variable (G : LatticeGraph)

theorem OAI.CriticalZ3.LatticeGraph.bondConn_iff_hypergraph (ω : BondConfig) (x y : G.Node) :
    G.BondConn ω x y ↔ HyperedgeComparison.Connected G.hypergraph
      (fun e => ω e.1) ∅ x y := by sorry
