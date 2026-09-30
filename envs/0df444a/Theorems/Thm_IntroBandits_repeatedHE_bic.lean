-- Prove2me | Theorems.Thm_IntroBandits_repeatedHE_bic
-- name    : IntroBandits.repeatedHE_bic
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-24T02:37:05.856163+00:00
-- url     : https://prove2.me/theorems/0b14088d-176f-424e-9e97-cda0dc00144f
-- title:
--   Theorem 11.15: RepeatedHE with $\varepsilon > 0$ and $N_0$ initial samples of arm 1 is BIC as long as $\varepsilon < \frac13\mathbb{E}[G \cdot \mathbf 1\{G > 0\}]$, $G = G_{N_0+1}$
-- statement:
--   **Theorem 11.15.** RepeatedHE with exploration probability $\varepsilon > 0$ and $N_0$ initial samples of arm 1 is BIC as long as $\varepsilon < \frac13\,\mathbb{E}[G \cdot \mathbf 1\{G > 0\}]$, where $G = G_{N_0+1}$.
--
--   Formally: $P$ a prior (a probability measure on mean vectors) supported on the finite $F \subseteq [0,1]^2$ with $\mu^0_1 \ge \mu^0_2$; any reward family with finitely many reward values; any bandit algorithm $\mathrm{ALG}$; $N_0 \in \mathbb{N}$; $\varepsilon > 0$ with
--   $$\varepsilon < \frac13\sum_{s \in \mathrm{values}^{N_0}} \max\Big(0,\ \sum_{\mu \in F} P(\mu)\prod_{i \le N_0} D_{\mu_1}(\{s_i\})\,(\mu_2 - \mu_1)\Big) = \frac13\,\mathbb{E}[G \cdot \mathbf 1\{G > 0\}],$$
--   $G = \mathbb{E}[\mu_2 - \mu_1 \mid S_{1,N_0}]$ the posterior gap given the $N_0$ initial samples of arm 1. Then, for every horizon $T$, RepeatedHE (Algorithm 11.2, run with $\mathrm{ALG}$, $N_0$, $\varepsilon$) is Bayesian incentive-compatible in the sense of Definition 11.4: for every round $t \le T$ and every two distinct arms $a, a'$ such that $\Pr[\mathrm{rec}_t = a] > 0$ under the law of the compliant run,
--   $$\mathbb{E}\big[(\mu_a - \mu_{a'})\,\mathbf 1\{\mathrm{rec}_t = a\}\big] \ge 0, \quad\text{i.e.}\quad \mathbb{E}[\mu_a - \mu_{a'} \mid \mathrm{rec}_t = a] \ge 0 .$$
--
--   **Reading.** The event $E_{t-1}$ of (11.1) is the sure event of the compliant law. The initial rounds recommend arm 1, so for them the condition reads $\mu^0_1 \ge \mu^0_2$; every later round is a HiddenExploration with signal $S_t$ (Lemma 11.10), and $\mathbb{E}[G_t \mathbf 1\{G_t > 0\}]$ is nondecreasing in $t$ because $S_{t+1}$ determines $S_t$. Nothing is assumed about $\mathrm{ALG}$; when $\mathbb{E}[G \mathbf 1\{G > 0\}] = 0$ no $\varepsilon$ qualifies (Remark 11.16).
-- source:
--   Slivkins, Introduction to Multi-Armed Bandits, arXiv:1904.07272 (FnT ML 12, 2019), §11.4 p. 151, Theorem 11.15 with its proof (monotonicity of E[G_t 1{G_t > 0}])

import Definitions.Def_IntroBandits_Agents

open MeasureTheory ProbabilityTheory BanditAlgorithm

namespace IntroBandits

theorem repeatedHE_bic (P : Measure (Fin 2 → ℝ)) [IsProbabilityMeasure P]
    (F : Finset (Fin 2 → ℝ)) (hF : P (↑F)ᶜ = 0)
    (hunit : ∀ μ ∈ F, ∀ a, μ a ∈ Set.Icc (0 : ℝ) 1) (fam : RewardFamily)
    (hprior : priorMean P F 1 ≤ priorMean P F 0) (A : BanditPolicy 2) (N₀ : ℕ) {ε : ℝ}
    (hε : 0 < ε) (hε3 : ε < initialGapPlus P F fam N₀ / 3) (T : ℕ) :
    IsBIC F (repeatedHELaw P F fam A N₀ ε T) recHE := by sorry

end IntroBandits
