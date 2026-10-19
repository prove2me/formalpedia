-- Prove2me | Theorems.Thm_OAI_CriticalZ3_LatticeGraph_lift_path
-- name    : OAI.CriticalZ3.LatticeGraph.lift_path
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:16:10.792473+00:00
-- url     : https://prove2.me/theorems/9696f57f-75ec-4e70-ae41-54b0bc0ac324
-- title:
--   Lifting paths into the vertex type of a lattice graph
-- statement:
--   A finite lattice graph $G$ is a finite set of vertices of $\mathbb Z^3$ with finitely many bonds between them; bond percolation on $G$ uses the product law on its bonds. Let $r$ be a relation on $\mathbb Z^3$ whose steps end at vertices of $G$, and $s$ a relation on the vertices of $G$ containing every $r$-step between them. If $x,y$ are vertices of $G$ joined by an $r$-path, then they are joined by an $s$-path:
--   $$
--   x\leadsto_ry\ \Longrightarrow\ x\leadsto_sy .
--   $$
--
--   It moves paths in $\mathbb Z^3$ into the finite graph $G$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/LatticePaths.lean#L155-L172

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison
import Definitions.Def_OAI_Probability_CriticalZ3_LatticeGraph
import Definitions.Def_OAI_Probability_CriticalZ3_BoxGeometry
import Definitions.Def_OAI_Probability_CriticalZ3_LatticePaths

open OAI OAI.CriticalZ3 OAI.CriticalZ3.LatticeGraph
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open Classical
variable (G : LatticeGraph)

theorem OAI.CriticalZ3.LatticeGraph.lift_path {r : Vertex → Vertex → Prop} {s : G.Node → G.Node → Prop}
    (hmem : ∀ x y, r x y → y ∈ G.vertices)
    (hrel : ∀ (x y : G.Node), r x.1 y.1 → s x y)
    {x y : G.Node} (h : Relation.ReflTransGen r x.1 y.1) : Relation.ReflTransGen s x y := by sorry
