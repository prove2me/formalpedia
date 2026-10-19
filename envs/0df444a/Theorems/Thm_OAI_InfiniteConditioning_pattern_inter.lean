-- Prove2me | Theorems.Thm_OAI_InfiniteConditioning_pattern_inter
-- name    : OAI.InfiniteConditioning.pattern_inter
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:19:43.165958+00:00
-- url     : https://prove2.me/theorems/e3ca1c15-5e8c-4352-bb2a-321a8e98ed54
-- title:
--   Product formula for a pattern and an event
-- statement:
--   Let $\mathbb P_p$ be the product Bernoulli law on $\{0,1\}^E$ (countable $E$), $J\subseteq E$ finite, and for revealed values $\xi$ let $p^{J,\xi}$ be the parameters fixing the bits of $J$ to $\xi$ and keeping $p_e$ elsewhere; the pattern of $\xi$ on $J$ is the cylinder $\{\omega:\omega|_J=\xi|_J\}$. For every measurable event $A$,
--   $$
--   \mathbb P_p(\text{pattern}_J(\xi)\cap A)=\mathbb P_p(\text{pattern}_J(\xi))\cdot\mathbb P_{p^{J,\xi}}(A).
--   $$
--
--   Conditionally on the revealed bits, the configuration has the modified product law.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/Conditioning.lean#L89-L110

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

open OAI OAI.InfiniteConditioning
universe uF
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
open MeasureTheory ProbabilityTheory Classical
variable {E : Type} [Countable E]

theorem OAI.InfiniteConditioning.pattern_inter (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E) (ξ : E → Bool)
    (A : Set (E → Bool)) (hA : MeasurableSet A) :
    ProductCylinder.law p (pattern J ξ ∩ A) =
      ProductCylinder.law p (pattern J ξ) * ProductCylinder.law (fixedParameter p J ξ) A := by sorry
