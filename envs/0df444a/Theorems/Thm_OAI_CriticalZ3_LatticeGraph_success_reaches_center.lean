-- Prove2me | Theorems.Thm_OAI_CriticalZ3_LatticeGraph_success_reaches_center
-- name    : OAI.CriticalZ3.LatticeGraph.success_reaches_center
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:18:35.410083+00:00
-- url     : https://prove2.me/theorems/930b490e-243c-4b11-ae49-9f5bd930eb2c
-- title:
--   An open success set connects an entrant to the relay centre
-- statement:
--   A finite lattice graph $G$ is a finite set of vertices of $\mathbb Z^3$ with finitely many bonds between them; bond percolation on $G$ uses the product law on its bonds. A box $B\subseteq\mathbb Z^3$ is a product of integer intervals; nearest neighbours differ by $\pm1$ in one coordinate. Let $C$ be wide enough for radius $r$ and suppose $G$ contains the expansion of $C$ by one. If $y$ is an entrant of the outside exploration from $o$ and all success bits of $y$ are open, then $o$ is connected in $G$ to the relay centre of $y$:
--   $$
--   o\leadsto\mathrm{relay}(y).
--   $$
--
--   A successful seed trial thus relays the cluster to the interior of $C$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/SeedTrials.lean#L131-L158

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
import Definitions.Def_OAI_Probability_CriticalZ3_SeedTrials

open OAI OAI.CriticalZ3 OAI.CriticalZ3.LatticeGraph
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open Classical
variable (G : LatticeGraph)

theorem OAI.CriticalZ3.LatticeGraph.success_reaches_center (m : Model) (C : Box) (r : ℕ)
    (hw : ∀ i, C.lower i+r ≤ C.upper i-r) (hC : G.ContainsBox (C.expand 1))
    {ω : m.Config} {o y : G.Node} (hy : y.1 ∈ G.entrants m C ω o)
    (hs : ∀ e ∈ C.successBits r m y.1, ω e = true) :
    ∃ v : G.Node, v.1 = C.relayCenter r y.1 ∧ G.Conn m ω o v := by sorry
