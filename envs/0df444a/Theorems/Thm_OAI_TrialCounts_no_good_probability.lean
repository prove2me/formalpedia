-- Prove2me | Theorems.Thm_OAI_TrialCounts_no_good_probability
-- name    : OAI.TrialCounts.no_good_probability
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:26:09.876589+00:00
-- url     : https://prove2.me/theorems/7bbfc9bc-5fa0-42c0-8c77-150b0186f087
-- title:
--   Probability that all successes are bad
-- statement:
--   Let $A_i$ be success events of equal probability $c$ with $\mu(A_i\cap A_j)\le c^2$ for $i\ne j$, and $B_i$ bad events with $\mu(B_i)\le c\gamma/\tau$, over a finite index set $I$ with $|I|c>0$ and $\tau>0$. Then the probability that every success is bad satisfies
--   $$
--   \mu\bigl(\forall i:\ A_i\Rightarrow B_i\bigr)\le\frac4{|I|c}+\frac{2\gamma}\tau .
--   $$
--
--   It combines a second-moment bound on successes with a first-moment bound on bad successes.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/TrialCounts.lean#L154-L188

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

theorem OAI.TrialCounts.no_good_probability (A B : I → Set Ω)
    (hA : ∀ i, MeasurableSet (A i)) (hB : ∀ i, MeasurableSet (B i))
    {c γ τ : ℝ} (hcpos : 0 < Fintype.card I*c) (hτ : 0 < τ)
    (hc : ∀ i, μ.real (A i) = c)
    (hpair : ∀ i j, i ≠ j → μ.real (A i ∩ A j) ≤ c*c)
    (hbad : ∀ i, μ.real (B i) ≤ c*γ/τ) :
    μ.real {ω | ∀ i, ω ∈ A i → ω ∈ B i} ≤ 4/(Fintype.card I*c)+2*γ/τ := by sorry
