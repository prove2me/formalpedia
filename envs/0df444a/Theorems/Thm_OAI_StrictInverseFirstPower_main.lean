-- Prove2me | Theorems.Thm_OAI_StrictInverseFirstPower_main
-- name    : OAI.StrictInverseFirstPower.main
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:26.735578+00:00
-- url     : https://prove2.me/theorems/9ae259b0-326c-43b3-90d9-840a003a3ea6
-- statement:
--   The theorem states a conjunction of three claims about the integral means of the derivative to the power -1 for normalized univalent functions on the unit disk. Here a function f:ℂ→ℂ is normalized univalent if it is complex-differentiable on the open unit disk, injective there, and satisfies f(0)=0 and f'(0)=1. The integral mean of order p at radius r is (2π)⁻¹ times the integral over θ from −π to π of |f'(re^{iθ})|^p. First, there exist real numbers ε and C with 0<ε<1/4 such that, for every normalized univalent f and every r with 1/2≤r<1, the order −1 integral mean of f at r is at most C(1−r)^(−1/4+ε). Second, the bounded spectrum at p=−1 is strictly less than 1/4 in the extended reals; this spectrum is the supremum, over normalized univalent f that are also bounded on the disk, of the growth exponent, which is the limsup as r→1⁻ of log(integral mean of order p at r) divided by log(1/(1−r)). Third, it is not the case that the bounded spectrum equals the prediction function kraetzerPrediction for every real p, where that function is p²/4 when |p|≤2 and |p|−1 otherwise.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/StrictMeans.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/StrictMeans.lean; bytes 1118..1482
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_StrictMeans

namespace OAI

open Set Filter MeasureTheory

open scoped Topology

namespace StrictInverseFirstPower

theorem main :
    (∃ ε C : ℝ, 0 < ε ∧ ε < 1 / 4 ∧
      ∀ (f : ℂ → ℂ), NormalizedUnivalent f →
        ∀ r : ℝ, 1 / 2 ≤ r → r < 1 →
          integralMean (-1) f r ≤ C * (1 - r) ^ (-(1 / 4 : ℝ) + ε)) ∧
    boundedSpectrum (-1) < (1 / 4 : EReal) ∧
    (¬ ∀ p : ℝ, boundedSpectrum p = kraetzerPrediction p) := by
  sorry

end StrictInverseFirstPower
end OAI
