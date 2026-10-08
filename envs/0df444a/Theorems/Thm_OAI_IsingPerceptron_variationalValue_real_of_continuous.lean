-- Prove2me | Theorems.Thm_OAI_IsingPerceptron_variationalValue_real_of_continuous
-- name    : OAI.IsingPerceptron.variationalValue_real_of_continuous
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:48.837983+00:00
-- url     : https://prove2.me/theorems/6880329e-d857-4e2a-ae54-7a208c3f82fa
-- statement:
--   The theorem states that, for every real α ≥ 0 and every continuous function f : ℝ → ℝ that is bounded (there is K with |f(x)| ≤ K for all x), the variational value of the Ising perceptron model is a finite real number, i.e. variationalValue(α,f) equals the extended real (p : EReal) for some real p. Here variationalValue(α,f) is the infimum, over all admissible overlap paths q (almost-everywhere-defined functions on (0,1) that agree a.e. with a monotone function taking values in [0,1]), of α times the pattern functional of f at q plus the Ising entropy of q. The pattern functional is the limit as n→∞ of uniformPattern, a nested Gaussian transform over a uniform grid with n+1 cells built from cell averages of q and applied to f at 0, where each transform is either a Gaussian average or a log-exponential-moment average divided by d, depending on whether d is zero. The Ising entropy is the supremum, over field steps (a partition of [0,1] with nonnegative monotone step values), of the field recursion value plus half the integral of the step function against q. The statement asserts that this infimum is neither +∞ nor −∞.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/IsingFiniteness.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/IsingFiniteness.lean; bytes 2672..2899
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_IsingFiniteness

namespace OAI

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators Topology ENNReal

noncomputable section

namespace IsingPerceptron

theorem variationalValue_real_of_continuous {α : ℝ} (hα : 0 ≤ α)
    {f : ℝ → ℝ} (hf : Continuous f) (hbounded : ∃ K : ℝ, ∀ x, |f x| ≤ K) :
    ∃ p : ℝ, variationalValue α f = (p : EReal) := by
  sorry

end IsingPerceptron
end
end OAI
