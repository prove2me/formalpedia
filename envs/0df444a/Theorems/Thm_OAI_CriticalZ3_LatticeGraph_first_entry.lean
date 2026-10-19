-- Prove2me | Theorems.Thm_OAI_CriticalZ3_LatticeGraph_first_entry
-- name    : OAI.CriticalZ3.LatticeGraph.first_entry
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:16:49.521201+00:00
-- url     : https://prove2.me/theorems/d541d807-3669-4944-8271-7c5d267960de
-- title:
--   A connection into a box enters through an entrant
-- statement:
--   A finite lattice graph $G$ is a finite set of vertices of $\mathbb Z^3$ with finitely many bonds between them; bond percolation on $G$ uses the product law on its bonds. A box $B\subseteq\mathbb Z^3$ is a product of integer intervals; nearest neighbours differ by $\pm1$ in one coordinate. For either percolation model, if a vertex $o$ outside a box $C$ is connected in $G$ to a vertex $z$ inside $C$, then there are vertices $y\notin C$ and $w\in C$ such that $y$ is an entrant of the outside exploration from $o$ and $y,w$ are adjacent in the configuration:
--   $$
--   o\leadsto y\ \text{outside }C,\qquad y\sim w,\qquad w\in C .
--   $$
--
--   Every cluster entering $C$ is therefore detected by the entry layer.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/EntryLayers.lean#L118-L136

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
import Definitions.Def_OAI_Probability_CriticalZ3_EntryLayers

open OAI OAI.CriticalZ3 OAI.CriticalZ3.LatticeGraph
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open Classical
variable (G : LatticeGraph)

theorem OAI.CriticalZ3.LatticeGraph.first_entry (m : Model) {C : Box} {ω : m.Config} {o z : G.Node}
    (ho : ¬C.Contains o.1) (hz : C.Contains z.1) (h : G.Conn m ω o z) :
    ∃ y w : G.Node, y.1 ∈ G.entrants m C ω o ∧ C.Contains w.1 ∧ G.Adj m ω y w := by sorry
