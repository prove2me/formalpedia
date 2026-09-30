-- Prove2me | Theorems.Thm_IntroBandits_hidden_exploration_bic
-- name    : IntroBandits.hidden_exploration_bic
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T02:34:54.248287+00:00
-- url     : https://prove2.me/theorems/1c8fd783-e39a-40f4-b3ea-34ea18fb66ee
-- title:
--   Lemma 11.10: HiddenExploration is BIC for any target function as long as $\varepsilon \le \frac13\mathbb{E}[G \cdot \mathbf 1\{G > 0\}]$
-- statement:
--   **Lemma 11.10.** Algorithm 11.1 is BIC, for any target function $a_{\mathrm{trg}}$, as long as $\varepsilon \le \frac13\,\mathbb{E}[G \cdot \mathbf 1\{G > 0\}]$, where $G = \mathbb{E}[\mu_2 - \mu_1 \mid \mathrm{sig}]$ is the posterior gap.
--
--   Formally: $\Omega$ a finite signal space and $Q$ a probability law of $(\mu, \mathrm{sig})$ whose $\mu$-marginal is supported on the finite $F \subseteq [0,1]^2$ with $\mu^0_1 \ge \mu^0_2$ (the standing assumption of the chapter's Preliminaries); $\mathrm{trg}$ any randomized target, a distribution over the two arms for each signal; $0 < \varepsilon \le \frac13 \sum_S \max\big(0, \mathbb{E}[(\mu_2 - \mu_1)\mathbf 1\{\mathrm{sig} = S\}]\big)$. Then the recommendation rule of HiddenExploration, $\Pr[\mathrm{rec} = a \mid \mathrm{sig} = S] = \varepsilon\,\mathrm{trg}(S)(a) + (1-\varepsilon)\mathbf 1\{a = \min\arg\max_{a'} \mathbb{E}[\mu_{a'} \mid \mathrm{sig} = S]\}$, satisfies the single-round BIC property (11.5): for both orderings of the two arms, $\Pr[\mathrm{rec} = a] > 0$ implies $\mathbb{E}[(\mu_a - \mu_{a'})\mathbf 1\{\mathrm{rec} = a\}] \ge 0$.
--
--   The bound is the printed one (non-strict); the book's proof ends with the strict $\varepsilon < \frac13 F(G > 0)$ because it proves the strict inequality (11.6), and at equality the same computation gives $\ge 0$, which is what (11.5) asks.
-- source:
--   Slivkins, Introduction to Multi-Armed Bandits, arXiv:1904.07272 (FnT ML 12, 2019), §11.3 p. 149, Lemma 11.10, with the proof on pp. 149-150

import Definitions.Def_IntroBandits_Agents

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace IntroBandits

theorem hidden_exploration_bic {Ω : Type} [Fintype Ω] [DecidableEq Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (Q : Measure ((Fin 2 → ℝ) × Ω)) [IsProbabilityMeasure Q]
    (F : Finset (Fin 2 → ℝ)) (hF : Q ((↑F)ᶜ ×ˢ Set.univ) = 0)
    (hunit : ∀ μ ∈ F, ∀ a, μ a ∈ Set.Icc (0 : ℝ) 1)
    (hprior : priorMean Q.fst F 1 ≤ priorMean Q.fst F 0)
    (trg : Ω → Fin 2 → ℝ) (htrg : ∀ S, trg S ∈ stdSimplex ℝ (Fin 2))
    {ε : ℝ} (hε : 0 < ε) (hε3 : ε ≤ sigGapPlus Q F / 3) :
    IsSingleRoundBIC Q F (hiddenExploration ε trg Q F) := by sorry

end IntroBandits
