-- Prove2me | Theorems.Thm_OAI_InfiniteConditioning_measure_select
-- name    : OAI.InfiniteConditioning.measure_select
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:20:21.333828+00:00
-- url     : https://prove2.me/theorems/69321324-c071-4c2e-9ee3-3dd34608446d
-- title:
--   Decomposing an event selected by revealed values
-- statement:
--   Let $\mathbb P_p$ be the product Bernoulli law on $\{0,1\}^E$ (countable $E$), $J\subseteq E$ finite, and for revealed values $\xi$ let $p^{J,\xi}$ be the parameters fixing the bits of $J$ to $\xi$ and keeping $p_e$ elsewhere; the pattern of $\xi$ on $J$ is the cylinder $\{\omega:\omega|_J=\xi|_J\}$. For measurable events $A(a)$ indexed by the possible values $a$ of the bits in $J$,
--   $$
--   \mathbb P_p\bigl(\omega\in A(\omega|_J)\bigr)=\sum_a\mathbb P_p(\text{pattern}_J(a))\cdot\mathbb P_{p^{J,a}}(A(a)).
--   $$
--
--   This is the law of total probability over the revealed values.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/Conditioning.lean#L129-L147

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

theorem OAI.InfiniteConditioning.measure_select (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E)
    (A : (J → Bool) → Set (E → Bool)) (hA : ∀ a, MeasurableSet (A a)) :
    (ProductCylinder.law p).real {ω | ω ∈ A (J.restrict ω)} =
      ∑ a : J → Bool, (ProductCylinder.law p).real (pattern J (ProductCylinder.extend J a)) *
        (ProductCylinder.law (fixedParameter p J (ProductCylinder.extend J a))).real (A a) := by sorry
