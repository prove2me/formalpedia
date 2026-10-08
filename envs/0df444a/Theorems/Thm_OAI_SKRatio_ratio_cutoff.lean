-- Prove2me | Theorems.Thm_OAI_SKRatio_ratio_cutoff
-- name    : OAI.SKRatio.ratio_cutoff
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:18.134336+00:00
-- url     : https://prove2.me/theorems/d964735c-c00d-4f54-b120-998bf20bf6b4
-- statement:
--   The theorem states that, for real parameters β with 0 ≤ β < 1/2, ε with 0 < ε < 1/2, and η > 0, two things hold for the Sherrington–Kirkpatrick model with n spins, where a disorder g is a real coupling for each pair i < j of sites and the Gibbs measure at zero external field has weight proportional to exp((1/2) Σᵢ Σⱼ σᵢ gᵢⱼ σⱼ) on spin configurations σ ∈ {±1}ⁿ (couplings symmetrized, diagonal zero). The dynamics is a heat-bath single-site chain: choose a site uniformly at random, then keep or flip its spin with probabilities proportional to the Gibbs masses of the two configurations (for n = 0 the transition matrix is the identity). The distance after k steps is the maximum over starting configurations of the total variation distance (half the ℓ¹ distance) between the k-step distribution and the Gibbs measure, and mixingTime(g, δ) is the least k whose distance is at most δ (the infimum of the set, so 0 if that set is empty). The disorder law makes the couplings independent centered Gaussians with variance β²/n. First, the probability under this law that the ratio mixingTime(g, ε) / mixingTime(g, 1 − ε) exceeds 1 + η tends to 0 as n → ∞. Second, for all sufficiently large n, every disorder g satisfies mixingTime(g, 1 − ε) > 0.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/SKRatio.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/SKRatio.lean; bytes 2077..2489
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_SKRatio

namespace OAI

noncomputable section

open scoped BigOperators Topology

open MeasureTheory ProbabilityTheory Filter

namespace SKRatio

theorem ratio_cutoff (β ε η : ℝ)
    (hβ0 : 0 ≤ β) (hβhalf : β < 1 / 2)
    (hε0 : 0 < ε) (hεhalf : ε < 1 / 2) (hη : 0 < η) :
    Tendsto
      (fun n : ℕ => disorderLaw β n
        {g : Disorder n | 1 + η <
          (mixingTime g ε : ℝ) / (mixingTime g (1 - ε) : ℝ)})
      atTop (𝓝 0) ∧
    (∀ᶠ n : ℕ in atTop, ∀ g : Disorder n, 0 < mixingTime g (1 - ε)) := by
  sorry

end SKRatio
end
end OAI
