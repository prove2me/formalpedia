-- Prove2me | Theorems.Thm_LightTailBandit_ucb_regret_on_good_event
-- name    : LightTailBandit.ucb_regret_on_good_event
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:25:47.295003+00:00
-- url     : https://prove2.me/theorems/077e4679-61e1-4a2e-b934-2e92cf3d6dca
-- title:
--   Proof of Theorem 5, App. pp.18–19 — on $G$, UCB has pseudo regret at most $K+4\sigma\sqrt{(\eta_1\vee\eta_2)KT\ln T}$
-- statement:
--   Throughout, $K\ge2$ arms and a horizon $T$ with $T\ge3$ and $T\ge K$ are fixed, $\sigma>0$, rounds are $t=1,\dots,T$, and the reward of round $t$ is $r_{t,a_t}=\theta_{a_t}+\epsilon_{t,a_t}$, where the noise $\epsilon_{t,k}$ of round $t$ and arm $k$ is independent of everything observed before round $t$ and is $\sigma$-sub-Gaussian: $\mathbb E[e^{\lambda\epsilon_{t,k}}]\le e^{\lambda^2\sigma^2/2}$ for all real $\lambda$. The action $a_t$ may depend only on the past (and on independent internal randomization). $n_k$ is the number of pulls of arm $k$ in the $T$ rounds, $\theta_*=\max_k\theta_k$, $\Delta_k=\theta_*-\theta_k\le1$, and the bonus is $\mathrm{rad}(n)=\sigma\sqrt{\ln T/n}\,\max\{\sqrt{\eta_1T/(nK)},\sqrt{\eta_2}\}$ (6).
--
--   Let $\eta_1,\eta_2\ge0$ and consider any sample path of UCB with the bonus (6). If the good event $G$ holds on the path, then
--   $$
--   R(T)=\sum_{k=1}^Kn_k\Delta_k\le K+4\sigma\sqrt{\max\{\eta_1,\eta_2\}\,KT\ln T}.
--   $$
--
--   Adding $T\cdot P(\bar G)\le2K$ gives part 1 of Theorem 5 for UCB (with room to spare).
--
--   **Formalization Note** The statement is deterministic: it holds for every noise path and every run.
--
--   Differences from the source:
--   - generalization: E[R] ≤ E[Σ_{k∈S} n_kΔ_k | G] + E[Σ_{k∉A₀} n_kΔ_k | G] + 2K ≤ 3K + 2σ√(T ln T)(…) ≤ 4K + 4σ√((η₁∨η₂)KT ln T), for E under UCB → on every UCB path in G: R(T) ≤ K + 4σ√(max(η₁,η₂)KT ln T); reason: the pathwise bound on G implies the bound on the conditional expectations given G; with T·P(Ḡ) ≤ 2K (item prob_not_good_event, η₂ ≥ 4) it gives the printed line
--   - generalization: η₁, η₂ ≥ 4 (part 1 of Theorem 5) → η₁, η₂ ≥ 0; reason: the pathwise bound holds for all nonnegative tuning parameters
--   - generalization: Algorithm 2 'randomly select[s] one if a tie happens' → IsUCBRun: any tie-break, deterministic or randomized, on every sample path; reason: every run of Algorithm 2 satisfies the predicate; the proof never uses the tie rule
--   - reading: UCB index θ̂_{t−1,k} + rad(n_{t−1,k}) at an unpulled arm (rad(0) undefined) → while some arm is unpulled, UCB pulls an unpulled arm (the convention rad(0) = +∞); reason: the page leaves the index of an unsampled arm undefined; the proof uses that arm 1 has been sampled when arm k is pulled for the (n₀+1)-st time
--   - encoding: rounds t = 1, …, T and arms [K] → rounds 0, …, T − 1 (Lean round t is the paper's round t + 1) and Fin K; reason: Lean convention; same instances
-- source:
--   Simchi-Levi, Zheng, Zhu, A Simple and Optimal Policy Design with Safety against Heavy-Tailed Risk for Stochastic Bandits, arXiv:2206.02969v6, Online Appendix, proof of Theorem 5, part 1(b), pp.18–19 (PDF pp.55–56)

import Mathlib
import Definitions.Def_FoundationsRL_Bandits_pullCount
import Definitions.Def_LightTailBandit_IsNoiseModel
import Definitions.Def_LightTailBandit_reward
import Definitions.Def_LightTailBandit_pseudoRegret
import Definitions.Def_LightTailBandit_rad
import Definitions.Def_LightTailBandit_IsUCBRun
import Definitions.Def_LightTailBandit_IsSERun
import Definitions.Def_LightTailBandit_goodEvent

open MeasureTheory ProbabilityTheory FoundationsRL.Bandits

namespace LightTailBandit

/-- **Regret of UCB on the good event** (Simchi-Levi, Zheng, Zhu, *A Simple and Optimal Policy Design with Safety against Heavy-Tailed Risk
for Stochastic Bandits*, arXiv:2206.02969v6, Online Appendix, proof of
Theorem 5, part 1(b), pp.18–19 (PDF pp.55–56): "`E[R] ≤ … + 2K ≤ 3K + … ≤ 4K + 4σ√((η₁∨η₂)KT ln T)`").

Along every sample path of UCB with the bonus (6), with `η₁, η₂ ≥ 0` and gaps at most `1`, if the
good event `G` holds then the pseudo regret is at most `K + 4σ√(max(η₁,η₂) K T ln T)`.

**Formalization Note.** Rounds are 0-based (Lean round `t < T` is the paper's round `t + 1`), arms are `Fin K`, the
noise is a table `ε t k` with a filtration `ℱ` (`IsNoiseModel`), and σ-subGaussian is read as the
moment-generating-function condition with variance proxy `σ²`. The page bounds conditional expectations
given `G`; the statement is the pathwise bound on `G`. The printed `3K` is this `K` plus the `2K`
coming from `T · P(Ḡ)`. -/
theorem ucb_regret_on_good_event {K T : ℕ} (hK : 2 ≤ K) (hT : 3 ≤ T) (hKT : K ≤ T)
    {σ η₁ η₂ : ℝ} (hσ : 0 < σ) (hη₁ : 0 ≤ η₁) (hη₂ : 0 ≤ η₂)
    (θ : Fin K → ℝ) (hgap : ∀ k, gap θ k ≤ 1)
    (e : ℕ → Fin K → ℝ) (h : ℕ → Fin K)
    (hrun : IsUCBRun σ η₁ η₂ T θ e h) (hG : goodEvent σ η₁ η₂ T e h) :
    pseudoRegret θ T h ≤ K + 4 * σ * Real.sqrt (max η₁ η₂ * K * T * Real.log T) := by sorry

end LightTailBandit
