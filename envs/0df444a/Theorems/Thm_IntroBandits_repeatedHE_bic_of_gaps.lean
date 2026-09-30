-- Prove2me | Theorems.Thm_IntroBandits_repeatedHE_bic_of_gaps
-- name    : IntroBandits.repeatedHE_bic_of_gaps
-- status  : Open
-- author  : @naimengye
-- created : 2026-09-24T02:36:21.344073+00:00
-- url     : https://prove2.me/theorems/8e7429b0-b729-4cbc-bf5c-d4c2845ca9fc
-- title:
--   Corollary 11.14: RepeatedHE is BIC if $\varepsilon < \frac13\mathbb{E}[G_t \cdot \mathbf 1\{G_t > 0\}]$ for each time $t > N_0$
-- statement:
--   **Corollary 11.14.** RepeatedHE is BIC if $\varepsilon < \frac13\,\mathbb{E}[G_t \cdot \mathbf 1\{G_t > 0\}]$ for each time $t > N_0$, where $G_t = \mathbb{E}[\mu_2 - \mu_1 \mid S_t]$ is the posterior gap given the exploration data $S_t$.
--
--   Formally: $P$ a prior supported on the finite $F \subseteq [0,1]^2$ with $\mu^0_1 \ge \mu^0_2$, any reward family, any bandit algorithm $\mathrm{ALG}$, $N_0$ initial rounds, $\varepsilon > 0$ and a horizon $T$. If for every round of the run after the initial ones (record lengths $n$ with $N_0 \le n < T$) $\varepsilon < \frac13 \mathbb{E}[\max(0, G)]$, where $G$ is the posterior gap given the exploration rounds of the first $n$ rounds and the expectation is under the law of the first $n$ rounds of RepeatedHE, then RepeatedHE is BIC (Definition 11.4) over the $T$ rounds: for every round and every two distinct arms $a, a'$ with $\Pr[\mathrm{rec}_t = a] > 0$, $\mathbb{E}[(\mu_a - \mu_{a'})\mathbf 1\{\mathrm{rec}_t = a\}] \ge 0$ under the law of the compliant run.
-- source:
--   Slivkins, Introduction to Multi-Armed Bandits, arXiv:1904.07272 (FnT ML 12, 2019), §11.4 p. 151, Corollary 11.14 (Lemma 11.10 applied round by round with signal S_t)

import Definitions.Def_IntroBandits_Agents

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace IntroBandits

theorem repeatedHE_bic_of_gaps (P : Measure (Fin 2 → ℝ)) [IsProbabilityMeasure P]
    (F : Finset (Fin 2 → ℝ)) (hF : P (↑F)ᶜ = 0)
    (hunit : ∀ μ ∈ F, ∀ a, μ a ∈ Set.Icc (0 : ℝ) 1) (fam : RewardFamily)
    (hprior : priorMean P F 1 ≤ priorMean P F 0) (A : BanditPolicy 2) (N₀ : ℕ) {ε : ℝ}
    (hε : 0 < ε) {T : ℕ}
    (hgap : ∀ n, N₀ ≤ n → n < T →
      ε < heExpect P F fam A N₀ ε n (fun h ↦ max 0 (explGap P F fam h)) / 3) :
    IsBIC F (repeatedHELaw P F fam A N₀ ε T) recHE := by sorry

end IntroBandits
