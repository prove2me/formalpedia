-- Prove2me | Theorems.Thm_OAI_CriticalZ3_LatticeGraph_bondMeets_probability
-- name    : OAI.CriticalZ3.LatticeGraph.bondMeets_probability
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:12:21.803281+00:00
-- url     : https://prove2.me/theorems/be909cdc-19c4-4303-a405-4b0d0c20df77
-- title:
--   Bond meeting probabilities as hypergraph probabilities
-- statement:
--   A finite lattice graph $G$ is a finite set of vertices of $\mathbb Z^3$ with finitely many bonds between them; bond percolation on $G$ uses the product law on its bonds. For parameters $p$ on bonds, $o$ a vertex of $G$ and $T\subseteq\mathbb Z^3$, the probability under the infinite product law that $o$ meets $T$ within $G$ equals the corresponding probability for the finite bond hypergraph of $G$:
--   $$
--   \mathbb P_p(o\leadsto T\ \text{in }G)=\mathbb P^{\mathrm{hyp}}_{p|_{G}}(o\ \text{meets}\ T).
--   $$
--
--   It transfers the hypergraph comparison to bond percolation.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/LatticeGraph.lean#L144-L161

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

theorem OAI.CriticalZ3.LatticeGraph.bondMeets_probability (p : Bond → Set.Icc (0 : ℝ) 1)
    (o : G.Node) (T : Set Vertex) :
    (ProductCylinder.law p).real {ω | G.BondMeets ω o T} =
      HyperedgeComparison.eventProb (fun e : G.edges => p e.1)
        (fun ω => HyperedgeComparison.Meets G.hypergraph ω ∅ o {y | y.1 ∈ T}) := by sorry
