-- Prove2me | Theorems.Thm_OAI_InfiniteConditioning_conditional_failure_mass
-- name    : OAI.InfiniteConditioning.conditional_failure_mass
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:23:22.535842+00:00
-- url     : https://prove2.me/theorems/405ab270-cc47-4bca-afaf-c415f006f62e
-- title:
--   Markov bound for low conditional probabilities
-- statement:
--   Let $\mathbb P_p$ be a product Bernoulli law on $\{0,1\}^E$ and $J\subseteq E$ finite; $\mathbb P_p(C\mid\omega_J)$ denotes the probability of $C$ under the product law with the bits of $J$ fixed to their values in $\omega$. Let $H$ be determined by the bits in $J$, $C$ measurable and $\delta\ge0$. Then
--   $$
--   \delta\cdot\mathbb P_p\bigl(H\cap\{\mathbb P_p(C\mid\omega_J)\le1-\delta\}\bigr)\le\mathbb P_p(H\cap C^c).
--   $$
--
--   Revealed situations in which $C$ is unlikely are rare if $C$ rarely fails on $H$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/ConditionalQuality.lean#L25-L75

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

open OAI OAI.InfiniteConditioning
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open MeasureTheory ProbabilityTheory Classical
variable {E : Type} [Countable E]

theorem OAI.InfiniteConditioning.conditional_failure_mass (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E)
    (H C : Set (E → Bool))
    (hH : ProductCylinder.DeterminedBy (F := Prop) J (fun ω => ω ∈ H))
    (hC : MeasurableSet C) {δ : ℝ} (_hδ : 0 ≤ δ) :
    δ * (ProductCylinder.law p).real
      {ω | ω ∈ H ∧ conditionalProbability p J C ω ≤ 1-δ} ≤
    (ProductCylinder.law p).real (H ∩ Cᶜ) := by sorry
