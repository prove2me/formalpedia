-- Prove2me | Theorems.Thm_OAI_CriticalZ3_Box_connected
-- name    : OAI.CriticalZ3.Box.connected
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:15:20.468366+00:00
-- url     : https://prove2.me/theorems/a47b85df-5ab7-4daa-96ce-c99ee10416f1
-- title:
--   Boxes are connected by nearest-neighbour steps
-- statement:
--   A box $B\subseteq\mathbb Z^3$ is a product of integer intervals; nearest neighbours differ by $\pm1$ in one coordinate. Any two points $x,y$ of a box $B$ are joined by a path of nearest-neighbour steps staying inside $B$:
--   $$
--   x\leadsto y\ \text{within }B .
--   $$
--
--   In particular a fully open box is connected in either percolation model.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/BoxGeometry.lean#L376-L397

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

open OAI OAI.CriticalZ3 OAI.CriticalZ3.Box
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open Classical

theorem OAI.CriticalZ3.Box.connected (B : Box) {x y : Vertex} (hx : B.Contains x) (hy : B.Contains y) :
    Relation.ReflTransGen B.Within x y := by sorry
