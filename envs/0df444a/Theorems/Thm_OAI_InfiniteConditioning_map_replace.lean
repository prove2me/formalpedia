-- Prove2me | Theorems.Thm_OAI_InfiniteConditioning_map_replace
-- name    : OAI.InfiniteConditioning.map_replace
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:19:08.053287+00:00
-- url     : https://prove2.me/theorems/428a913f-1782-47df-9090-ff27efafae08
-- title:
--   Fixing finitely many bits pushes the product law to a modified product law
-- statement:
--   Let $\mathbb P_p$ be the product Bernoulli law on $\{0,1\}^E$ (countable $E$), $J\subseteq E$ finite, and for revealed values $\xi$ let $p^{J,\xi}$ be the parameters fixing the bits of $J$ to $\xi$ and keeping $p_e$ elsewhere; the pattern of $\xi$ on $J$ is the cylinder $\{\omega:\omega|_J=\xi|_J\}$. The image of $\mathbb P_p$ under the map replacing the bits in $J$ by $\xi$ is the product law with those bits fixed:
--   $$
--   (\mathrm{replace}_{J,\xi})_*\mathbb P_p=\mathbb P_{p^{J,\xi}} .
--   $$
--
--   This is the exact form of conditioning on revealed bits.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/Conditioning.lean#L48-L63

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

omit [Countable E] in
theorem OAI.InfiniteConditioning.map_replace (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E) (ξ : E → Bool) :
    (ProductCylinder.law p).map (replace J ξ) = ProductCylinder.law (fixedParameter p J ξ) := by sorry
