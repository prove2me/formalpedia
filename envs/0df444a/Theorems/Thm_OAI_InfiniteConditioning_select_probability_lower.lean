-- Prove2me | Theorems.Thm_OAI_InfiniteConditioning_select_probability_lower
-- name    : OAI.InfiniteConditioning.select_probability_lower
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T19:22:39.463826+00:00
-- url     : https://prove2.me/theorems/aaf222bd-5e0c-49ba-b996-2c7abbc349bf
-- title:
--   Lower bound for events selected after revealing bits
-- statement:
--   Let $\mathbb P_p$ be the product Bernoulli law on $\{0,1\}^E$ (countable $E$), $J\subseteq E$ finite, and for revealed values $\xi$ let $p^{J,\xi}$ be the parameters fixing the bits of $J$ to $\xi$ and keeping $p_e$ elsewhere; the pattern of $\xi$ on $J$ is the cylinder $\{\omega:\omega|_J=\xi|_J\}$. Let $P$ be a property of the revealed values on $J$ and $A(a)$ events such that $\mathbb P_{p^{J,a}}(A(a))\ge b$ whenever $P(a)$ holds. Then
--   $$
--   b\cdot\mathbb P_p\bigl(P(\omega|_J)\bigr)\le\mathbb P_p\bigl(P(\omega|_J)\ \text{and}\ \omega\in A(\omega|_J)\bigr).
--   $$
--
--   It is the step used when the exploration adapts to revealed information.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/Conditioning.lean#L361-L388

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

theorem OAI.InfiniteConditioning.select_probability_lower (p : E → Set.Icc (0 : ℝ) 1) (J : Finset E)
    (P : (J → Bool) → Prop) (A : (J → Bool) → Set (E → Bool))
    (hA : ∀ a, MeasurableSet (A a)) {b : ℝ}
    (hb : ∀ a, P a → b ≤
      (ProductCylinder.law (fixedParameter p J (ProductCylinder.extend J a))).real (A a)) :
    b * (ProductCylinder.law p).real {ω | P (J.restrict ω)} ≤
      (ProductCylinder.law p).real {ω | P (J.restrict ω) ∧ ω ∈ A (J.restrict ω)} := by sorry
