-- Prove2me | Theorems.Thm_OAI_ThorpCompatibility_clump_subset_sum
-- name    : OAI.ThorpCompatibility.clump_subset_sum
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T00:01:46.829382+00:00
-- url     : https://prove2.me/theorems/2c02420d-a8a2-4631-bcac-3bc11e21cb49
-- title:
--   Evaluating the one-cell clump-weight sum by subset size
-- statement:
--   Let $I$ be a finite set with $a=|I|$ elements and let $H,z,\rho\in\mathbb{R}$. For $s\subseteq I$ let the clump weight be $\phi_{H,z}(s)=1$ if $s=\varnothing$, $\phi_{H,z}(s)=e^{z|s|}$ if $s\ne\varnothing$ and $|s|>H$, and $\phi_{H,z}(s)=0$ otherwise. Then
--   $$
--   \sum_{s\subseteq I}\phi_{H,z}(s)\,\rho^{|s|}=1+\sum_{\substack{1\le h\le a\\ h>H}}\binom{a}{h}\big(e^{z}\rho\big)^{h}.
--   $$
--
--   The left side is the one-cell factor in the product bound for the exponential moment of the clump count. The identity turns it into a tail of a binomial sum, which can then be bounded term by term when $e^{z}\rho$ is small.
--
--   **Formalization Note** In Lean the right side is a sum over $h\in\{0,\dots,a\}$ of `if h = 0 then 1 else if H < h then (a.choose h) * (exp z * ρ)^h else 0`, and the comparison $H<h$ is made in $\mathbb{R}$. No conditions on $H$, $z$ or $\rho$ are imposed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/ThorpCompatibility/BinomialBounds.lean#L93-L108

import Mathlib
import Definitions.Def_ThorpWeightedCompatibility
import Definitions.Def_OAI_Probability_ThorpCompatibility_FiniteLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Entropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_ConditionalEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_LightRescaling
import Definitions.Def_OAI_Probability_ThorpCompatibility_Prediction
import Definitions.Def_OAI_Probability_ThorpCompatibility_RankLaw
import Definitions.Def_OAI_Probability_ThorpCompatibility_Model
import Definitions.Def_OAI_Probability_ThorpCompatibility_EntropyChain
import Definitions.Def_OAI_Probability_ThorpCompatibility_GridEntropy
import Definitions.Def_OAI_Probability_ThorpCompatibility_GridExposure
import Definitions.Def_OAI_Probability_ThorpCompatibility_ClumpCost
import Definitions.Def_OAI_Probability_ThorpCompatibility_PermutationProbability
import Definitions.Def_OAI_Probability_ThorpCompatibility_ListIncidence
import Definitions.Def_OAI_Probability_ThorpCompatibility_ClumpMoments

open OAI OAI.ThorpCompatibility
open scoped Classical
open Finset
open Finset

theorem OAI.ThorpCompatibility.clump_subset_sum {α : Type*} [Fintype α] (H z ρ : ℝ) :
    (∑ s : Finset α, clumpWeight H z s * ρ ^ s.card) =
      ∑ h ∈ Finset.range (Fintype.card α + 1),
        if h = 0 then 1 else if H < h then
          (Nat.choose (Fintype.card α) h : ℝ) * (Real.exp z * ρ) ^ h else 0 := by sorry
