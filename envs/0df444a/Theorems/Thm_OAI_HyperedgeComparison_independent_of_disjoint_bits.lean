-- Prove2me | Theorems.Thm_OAI_HyperedgeComparison_independent_of_disjoint_bits
-- name    : OAI.HyperedgeComparison.independent_of_disjoint_bits
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:57:32.678962+00:00
-- url     : https://prove2.me/theorems/0619bf07-d96c-454b-9b61-6f039840bb47
-- title:
--   Functions of disjoint bit sets are independent
-- statement:
--   Under a product Bernoulli law on finitely many bits, if $f$ depends only on the bits in $J$ and $g$ only on the bits outside $J$, then $f$ and $g$ are independent random variables:
--   $$
--   f\perp g .
--   $$
--
--   This is the basic independence of product measures.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/HyperedgeComparison.lean#L337-L363

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic
import Definitions.Def_OAI_Probability_CriticalZ3_ProductCylinder
import Definitions.Def_OAI_Probability_CriticalZ3_Symmetry
import Definitions.Def_OAI_Probability_CriticalZ3_QuarterFaces
import Definitions.Def_OAI_Probability_CriticalZ3_Resampling
import Definitions.Def_OAI_Probability_CriticalZ3_HyperedgeComparison

open OAI OAI.HyperedgeComparison
universe uE uI uV
open MeasureTheory ProbabilityTheory Classical Filter
open scoped ENNReal BigOperators Matrix
variable {V : Type uV} {E : Type uE}
variable [Fintype E]

theorem OAI.HyperedgeComparison.independent_of_disjoint_bits (p : E → Set.Icc (0 : ℝ) 1)
    (J : Finset E) (f g : (E → Bool) → ℝ)
    (hf : ∀ ω ω', (∀ e ∈ J, ω' e = ω e) → f ω' = f ω)
    (hg : ∀ ω ω', (∀ e ∉ J, ω' e = ω e) → g ω' = g ω) :
    IndepFun f g (law p) := by sorry
