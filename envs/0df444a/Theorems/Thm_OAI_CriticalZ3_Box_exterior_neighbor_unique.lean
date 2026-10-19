-- Prove2me | Theorems.Thm_OAI_CriticalZ3_Box_exterior_neighbor_unique
-- name    : OAI.CriticalZ3.Box.exterior_neighbor_unique
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:14:04.979007+00:00
-- url     : https://prove2.me/theorems/31a1e4e7-e655-481b-8743-dbf6b0520fc3
-- title:
--   An outside vertex has at most one neighbour in a box
-- statement:
--   A box $B\subseteq\mathbb Z^3$ is a product of integer intervals; nearest neighbours differ by $\pm1$ in one coordinate. If $y$ lies outside a box $B$ and $z,z'\in B$ are both nearest neighbours of $y$, then
--   $$
--   z=z' .
--   $$
--
--   So the entry point of an exterior vertex is well defined.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/BoxGeometry.lean#L102-L130

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

theorem OAI.CriticalZ3.Box.exterior_neighbor_unique (B : Box) {y z z' : Vertex}
    (hy : ¬ B.Contains y) (hz : B.Contains z) (hz' : B.Contains z')
    (hyz : NearestNeighbor y z) (hyz' : NearestNeighbor y z') : z = z' := by sorry
