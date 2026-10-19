-- Prove2me | Theorems.Thm_OAI_CriticalZ3_LatticeGraph_seed_conditional_quality
-- name    : OAI.CriticalZ3.LatticeGraph.seed_conditional_quality
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:31:02.993149+00:00
-- url     : https://prove2.me/theorems/126889c9-8af5-4857-b78e-2c5655138cd3
-- title:
--   Open seeds are rarely of low conditional quality
-- statement:
--   Work with bond or site percolation on a finite lattice graph $G\subseteq\mathbb Z^3$ under a product law $\mathbb P_p$; "$o\leadsto T$" means that $o$ is connected in $G$ to a vertex of $T$. Boxes $C$ have bits (bonds or sites), exterior vertices adjacent to them, and entry bits. Let $\Lambda_a(c)\subseteq C$, $a\le b$, $G\supseteq\Lambda_b(c)$, $v=c$, and suppose the seed crossing to $T$ has probability at least $1-\gamma$. Then for $\tau>0$,
--   $$
--   \mathbb P_p\bigl(\Lambda_a(c)\ \text{open},\ \mathbb P_p(v\leadsto T\mid\omega_C)\le1-\tau\bigr)\le\mathbb P_p(\Lambda_a(c)\ \text{open})\,\frac\gamma\tau .
--   $$
--
--   Seed trials that succeed are therefore usually good relays.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/SeedQuality.lean#L113-L135

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
import Definitions.Def_OAI_Probability_CriticalZ3_Conditioning
import Definitions.Def_OAI_Probability_CriticalZ3_ConditionalQuality
import Definitions.Def_OAI_Probability_CriticalZ3_TrialCounts
import Definitions.Def_OAI_Probability_CriticalZ3_ShellProbability
import Definitions.Def_OAI_Probability_CriticalZ3_SeedQuality

open OAI OAI.CriticalZ3 OAI.CriticalZ3.LatticeGraph
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
variable (G : LatticeGraph) (m : Model)

theorem OAI.CriticalZ3.LatticeGraph.seed_conditional_quality (p : m.Bit → Set.Icc (0 : ℝ) 1)
    (C : Box) (T : Set Vertex) {c : Vertex} {a b : ℕ} (hab : a ≤ b)
    (hseed : ∀ x, (Box.cube c a).Contains x → C.Contains x)
    (hB : G.ContainsBox (Box.cube c b)) (v : G.Node) (hv : v.1 = c)
    {γ τ : ℝ} (hτ : 0 < τ)
    (hprob : 1-γ ≤ (ProductCylinder.law p).real (m.SeedReaches c a b T)) :
    (ProductCylinder.law p).real
      {ω | ω ∈ allValue ((Box.cube c a).bits m) true ∧
        conditionalProbability p (C.bits m) {ω | G.Meets m ω v T} ω ≤ 1-τ} ≤
      (ProductCylinder.law p).real (allValue ((Box.cube c a).bits m) true)*γ/τ := by sorry
