-- Prove2me | Theorems.Thm_OAI_PlanarBoundary_finite_good_subset
-- name    : OAI.PlanarBoundary.finite_good_subset
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:54:11.777964+00:00
-- url     : https://prove2.me/theorems/8dd41c24-337c-4f2b-9c2f-cf8a8ed07b07
-- title:
--   A finite good region around the origin is enclosed by a blocked contour
-- statement:
--   A code of length $n$ is a starting column below $2n$, a starting row and a word of $n$ directions, tracing $n$ consecutive unit sides; it is valid if the traced sides are distinct boundary sides of some finite cell set. A code is blocked at $\omega$ if each traced side has a bad inner or outer cell. Suppose that whenever the set $\mathrm{Good}(\omega)$ of planar cells is finite, every cell outside it adjacent to a good cell is bad. Then the event that $\mathrm{Good}(\omega)$ is finite and contains $(0,0)$ is contained in the union over $n$ and valid codes $c$ of length $n$ of the events that $c$ is blocked:
--   $$
--   \{|\mathrm{Good}|<\infty,\ (0,0)\in\mathrm{Good}\}\subseteq\bigcup_n\bigcup_{c\ \text{valid}}\{c\ \text{blocked}\}.
--   $$
--
--   This is the Peierls contour argument for the coarse exploration.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/Peierls.lean#L111-L129

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

omit [MeasurableSpace Ω] in
theorem OAI.PlanarBoundary.finite_good_subset (Good : Ω → Set Point) (Bad : Point → Set Ω)
    (houtside : ∀ ω, (Good ω).Finite → ∀ x ∈ Good ω, ∀ d : Direction,
      x+outward d ∉ Good ω → ω ∈ Bad (x+outward d)) :
    {ω | (Good ω).Finite ∧ (0,0) ∈ Good ω} ⊆
      ⋃ n, ⋃ c : {c : Code n // Valid c}, candidate Bad c := by sorry
