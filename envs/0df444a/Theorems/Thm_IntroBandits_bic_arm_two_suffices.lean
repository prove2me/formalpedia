-- Prove2me | Theorems.Thm_IntroBandits_bic_arm_two_suffices
-- name    : IntroBandits.bic_arm_two_suffices
-- status  : Open
-- author  : @naimengye
-- created : 2026-09-24T02:35:24.896319+00:00
-- url     : https://prove2.me/theorems/23624dae-00ca-44b6-a5d1-56a27a6337e4
-- title:
--   Claim 11.12: if the single-round BIC property holds when arm 2 is recommended, it holds when arm 1 is
-- statement:
--   **Claim 11.12.** Assume (11.5) holds for arm $\mathrm{rec} = 2$. Then it also holds for $\mathrm{rec} = 1$.
--
--   Formally, for any recommendation rule that depends on the signal only: $\Omega$ finite, $Q$ a probability law of $(\mu, \mathrm{sig})$ with $\mu$-marginal supported on the finite $F$, $\mu^0_1 \ge \mu^0_2$, $\mathrm{rule}(S)$ a distribution over the two arms for each $S$. If $\Pr[\mathrm{rec} = 2] > 0$ implies $\mathbb{E}[(\mu_2 - \mu_1)\mathbf 1\{\mathrm{rec} = 2\}] \ge 0$, then the rule is single-round BIC: also $\Pr[\mathrm{rec} = 1] > 0$ implies $\mathbb{E}[(\mu_1 - \mu_2)\mathbf 1\{\mathrm{rec} = 1\}] \ge 0$. The proof is the identity $\mathbb{E}[\mu_2 - \mu_1] = \sum_a \mathbb{E}[(\mu_2 - \mu_1)\mathbf 1\{\mathrm{rec} = a\}]$ and $\mathbb{E}[\mu_2 - \mu_1] \le 0$.
-- source:
--   Slivkins, Introduction to Multi-Armed Bandits, arXiv:1904.07272 (FnT ML 12, 2019), §11.3 p. 149, Claim 11.12 with its proof

import Definitions.Def_IntroBandits_Agents

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace IntroBandits

theorem bic_arm_two_suffices {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (Q : Measure ((Fin 2 → ℝ) × Ω)) [IsProbabilityMeasure Q]
    (F : Finset (Fin 2 → ℝ)) (hF : Q ((↑F)ᶜ ×ˢ Set.univ) = 0)
    (hprior : priorMean Q.fst F 1 ≤ priorMean Q.fst F 0)
    (rule : Ω → Fin 2 → ℝ) (hrule : ∀ S, rule S ∈ stdSimplex ℝ (Fin 2))
    (h2 : 0 < ∑ S, (sigProb Q S).toReal * rule S 1 →
      0 ≤ ∑ μ ∈ F, ∑ S, (Q {(μ, S)}).toReal * (μ 1 - μ 0) * rule S 1) :
    IsSingleRoundBIC Q F rule := by sorry

end IntroBandits
