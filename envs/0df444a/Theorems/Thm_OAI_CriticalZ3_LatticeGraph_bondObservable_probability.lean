-- Prove2me | Theorems.Thm_OAI_CriticalZ3_LatticeGraph_bondObservable_probability
-- name    : OAI.CriticalZ3.LatticeGraph.bondObservable_probability
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:13:19.022992+00:00
-- url     : https://prove2.me/theorems/3a003425-9bfe-4e8b-9359-ad8c8039ed50
-- title:
--   Bond observables of meeting relations as hypergraph probabilities
-- statement:
--   A finite lattice graph $G$ is a finite set of vertices of $\mathbb Z^3$ with finitely many bonds between them; bond percolation on $G$ uses the product law on its bonds. More generally, for any property $\varphi$ of the whole meeting relation $(o,T)\mapsto[o\leadsto T\text{ in }G]$, the probability that the bond configuration satisfies $\varphi$ equals the probability that the hypergraph configuration satisfies $\varphi$:
--   $$
--   \mathbb P_p\bigl(\varphi(\leadsto_G)\bigr)=\mathbb P^{\mathrm{hyp}}_{p|_G}\bigl(\varphi(\text{meets})\bigr).
--   $$
--
--   Joint events such as meeting two targets are covered by this form.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/LatticeGraph.lean#L178-L203

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

theorem OAI.CriticalZ3.LatticeGraph.bondObservable_probability (p : Bond → Set.Icc (0 : ℝ) 1)
    (φ : (G.Node → Set Vertex → Prop) → Prop) :
    (ProductCylinder.law p).real {ω | φ (G.BondMeets ω)} =
      HyperedgeComparison.eventProb (fun e : G.edges => p e.1)
        (fun ω => φ (fun o T => HyperedgeComparison.Meets G.hypergraph ω ∅ o {y | y.1 ∈ T})) := by sorry
