-- Prove2me | Theorems.Thm_OAI_PlanarBoundary_blocked_bound
-- name    : OAI.PlanarBoundary.blocked_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:51:19.78164+00:00
-- url     : https://prove2.me/theorems/646eb963-0836-407c-9c62-f0a501e4877d
-- title:
--   Peierls bound for blocked contours
-- statement:
--   A code of length $n$ is a starting column below $2n$, a starting row and a word of $n$ directions, tracing $n$ consecutive unit sides; it is valid if the traced sides are distinct boundary sides of some finite cell set. A code is blocked at $\omega$ if each traced side has a bad inner or outer cell. Let bad events satisfy $\mu\bigl(\bigcap_{v\in s}\mathrm{Bad}(v)\bigr)\le f^{|s|}$ for every finite $s$, with $0<f\le\frac12$. Then every valid code of length $n$ satisfies
--   $$
--   \mu(\text{code blocked})\le(2f)^{n/7}.
--   $$
--
--   The exponent $n/7$ comes from the greedy packing of disjoint sides.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/Peierls.lean#L20-L64

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
import Definitions.Def_OAI_Probability_CriticalZ3_Scales
import Definitions.Def_OAI_Probability_CriticalZ3_Relay
import Definitions.Def_OAI_Probability_CriticalZ3_RelayProbability
import Definitions.Def_OAI_Probability_CriticalZ3_FiniteTrails
import Definitions.Def_OAI_Probability_CriticalZ3_PlanarBoundary
import Definitions.Def_OAI_Probability_CriticalZ3_Matching
import Definitions.Def_OAI_Probability_CriticalZ3_Peierls

open OAI OAI.PlanarBoundary
universe uOmega
open _root_.MeasureTheory ProbabilityTheory Classical Filter Topology Function
open scoped ENNReal BigOperators Matrix
open Filter Topology
open Classical _root_.MeasureTheory ProbabilityTheory
variable {Ω : Type uOmega} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem OAI.PlanarBoundary.blocked_bound {n : ℕ} (Bad : Point → Set Ω) (c : Code n) (hc : Valid c)
    {f : ℝ} (hf0 : 0 < f) (hf1 : 2*f ≤ 1)
    (hbad : ∀ s : Finset Point, μ.real {ω | ∀ v ∈ s, ω ∈ Bad v} ≤ f^s.card) :
    μ.real (blocked Bad c) ≤ (2*f)^((n : ℝ)/7) := by sorry
