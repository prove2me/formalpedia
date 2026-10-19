-- Prove2me | Theorems.Thm_OAI_TrialCounts_count_variance_le
-- name    : OAI.TrialCounts.count_variance_le
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:25:30.557601+00:00
-- url     : https://prove2.me/theorems/6626d98c-68b2-4d62-ada0-020f3296fec7
-- title:
--   Variance of a count of pairwise negatively correlated events
-- statement:
--   Let $A_i$, $i\in I$ finite, be events of equal probability $c$ that are pairwise at most independent: $\mu(A_i\cap A_j)\le c^2$ for $i\ne j$. Then the count $N=\sum_i\mathbf 1_{A_i}$ satisfies
--   $$
--   \mathrm{Var}(N)\le|I|\,c .
--   $$
--
--   Only pairwise information is needed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/TrialCounts.lean#L125-L152

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

open OAI OAI.TrialCounts
universe uI uOmega
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open MeasureTheory ProbabilityTheory Classical
open MeasureTheory ProbabilityTheory Classical
variable {Ω : Type uOmega} {I : Type uI} [MeasurableSpace Ω] [Fintype I]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem OAI.TrialCounts.count_variance_le (A : I → Set Ω) (hA : ∀ i, MeasurableSet (A i))
    {c : ℝ} (hc : ∀ i, μ.real (A i) = c)
    (hpair : ∀ i j, i ≠ j → μ.real (A i ∩ A j) ≤ c*c) :
    variance (count A) μ ≤ Fintype.card I*c := by sorry
