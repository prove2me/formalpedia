-- Prove2me | Theorems.Thm_OAI_CriticalZ3_LatticeGraph_random_relay_failure
-- name    : OAI.CriticalZ3.LatticeGraph.random_relay_failure
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:28:41.090553+00:00
-- url     : https://prove2.me/theorems/79e3cac3-1164-4980-bee4-d54a007e1e28
-- title:
--   Reaching good relays but not the target is unlikely
-- statement:
--   Work with bond or site percolation on a finite lattice graph $G\subseteq\mathbb Z^3$ under a product law $\mathbb P_p$; "$o\leadsto T$" means that $o$ is connected in $G$ to a vertex of $T$. Boxes $C$ have bits (bonds or sites), exterior vertices adjacent to them, and entry bits. Fix revealed bits $J$, a target $T$ and $\tau\ge0$, and call a vertex a good relay for $\omega$ if it reaches $T$ with conditional probability greater than $1-\tau$ given $\omega_J$. Then
--   $$
--   \mathbb P_p\bigl(o\leadsto\text{good relays}\ \text{and}\ o\not\leadsto T\bigr)\le\tau .
--   $$
--
--   This holds even though the set of good relays depends on the configuration.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/ShellProbability.lean#L266-L286

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

open OAI OAI.CriticalZ3 OAI.CriticalZ3.LatticeGraph
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open MeasureTheory ProbabilityTheory Classical InfiniteConditioning
variable (G : LatticeGraph) (m : Model)

theorem OAI.CriticalZ3.LatticeGraph.random_relay_failure (p : m.Bit → Set.Icc (0 : ℝ) 1) (J : Finset m.Bit)
    (o : G.Node) (T : Set Vertex) {τ : ℝ} (hτ : 0 ≤ τ) :
    (ProductCylinder.law p).real
      {ω | G.Meets m ω o (G.goodRelays m p J T τ ω) ∧ ¬G.Meets m ω o T} ≤ τ := by sorry
