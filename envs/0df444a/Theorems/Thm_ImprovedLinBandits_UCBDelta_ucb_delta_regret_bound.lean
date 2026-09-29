-- Prove2me | Theorems.Thm_ImprovedLinBandits_UCBDelta_ucb_delta_regret_bound
-- name    : ImprovedLinBandits.UCBDelta.ucb_delta_regret_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:24:15.18109+00:00
-- url     : https://prove2.me/theorems/00f7927a-d251-4d0b-a46e-cbdf90446335
-- title:
--   Theorem 7 — UCB($\delta$) has constant regret with probability at least $1-\delta$
-- statement:
--   Let $(\Omega, \mathcal F, P)$ be a probability space with a filtration $(\mathcal F_t)_{t \ge 0}$. Consider $d \ge 1$ arms with means $\mu_1, \dots, \mu_d \in \mathbb R$, best mean $\mu_* = \max_i \mu_i$ and gaps $\Delta_i = \mu_* - \mu_i$. In round $t \ge 1$ the arm $I_t$ is played and the reward $\mu_{I_t} + \eta_t$ is received, where
--
--   1. the noise $\eta_t$ is $\mathcal F_t$-measurable and conditionally $1$-sub-Gaussian, $\mathbf E[e^{\lambda\eta_t} \mid \mathcal F_{t-1}] \le e^{\lambda^2/2}$ for all $\lambda \in \mathbb R$;
--   2. the arm $I_t$ is $\mathcal F_{t-1}$-measurable and is chosen by UCB($\delta$): an arm not yet played if there is one, and otherwise an arm maximizing $\overline X_{j,t-1} + c_{j,t-1}$, with the widths $c$ of eq. (3) at the same level $\delta$.
--
--   Let $R_n = \sum_{t=1}^n (\mu_* - \mu_{I_t})$ be the pseudo-regret. Then for every $\delta > 0$, with probability at least $1 - \delta$, for all $n \ge 0$ simultaneously,
--   $$R_n \le \sum_{i : \Delta_i > 0}\left(3\Delta_i + \frac{16}{\Delta_i}\log\frac{2d}{\Delta_i\delta}\right).$$
--
--   The right-hand side does not depend on $n$: with high probability UCB($\delta$) incurs bounded regret over an infinite horizon. This is compatible with the Lai–Robbins logarithmic lower bound on the expected number of suboptimal plays, because the algorithm is tuned to a fixed $\delta$.
--
--   **Formalization Note** The failure event "$R_n$ exceeds the bound for some $n$" has outer probability at most $\delta$. The printed sentence carries no quantifier on $n$; the uniform-in-$n$ reading is the one matching the section's claim of constant regret and the time-uniform event of Lemma 6. The rule (4) is read with the statistics of rounds $1, \dots, t-1$, and an unplayed arm (width $+\infty$ in the paper) is played first. Measurability of $I_t$ with respect to $\mathcal F_{t-1}$ is assumed; it holds for any measurable tie-breaking rule. The hypothesis that $\Omega$ is a standard Borel space is added for Mathlib's conditional sub-Gaussianity. The sum runs over arms with $\Delta_i > 0$, so the divisions are well defined; the logarithm's argument may be below $1$, as in the paper. No bound on the means or on the rewards is assumed.
-- source:
--   Abbasi-Yadkori, Pál, Szepesvári, Improved Algorithms for Linear Stochastic Bandits, NIPS 2011, p. 7, Theorem 7 (with §6 eq. (3)–(4) and the pseudo-regret of §1.2, pp. 2–3)

import Mathlib
import Definitions.Def_ImprovedLinBandits_UCBDelta_armModel
import Definitions.Def_ImprovedLinBandits_UCBDelta_IsUCBDeltaRun

open MeasureTheory ProbabilityTheory

namespace ImprovedLinBandits.UCBDelta

/-- **Theorem 7** (Regret of UCB(δ); Abbasi-Yadkori, Pál, Szepesvári, NIPS 2011, p. 7). On a
`d`-armed bandit (`0 < d`) with means `μ`, gaps `Δ_i = μ_* - μ_i`, `ℱ_{t+1}`-measurable noise
`η (t + 1)` that is conditionally 1-sub-Gaussian given `ℱ_t`, and an `ℱ_t`-measurable arm
`I (t + 1)` chosen by UCB(δ) (`IsUCBDeltaRun`, with the same `δ` in the widths (3)), for every
`δ > 0` the (outer) probability that for some `n ≥ 0`
`R_n > ∑_{i : Δ_i > 0} (3 Δ_i + 16 / Δ_i · log(2 d / (Δ_i δ)))`
is at most `δ`. The bound thus holds for all `n` simultaneously on one event of probability at
least `1 - δ`. `StandardBorelSpace Ω` is added so that Mathlib's conditional sub-Gaussianity is
available; measurability of `I (t + 1)` is assumed (it holds for measurable tie-breaking). -/
theorem ucb_delta_regret_bound
    {Ω : Type} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {d : ℕ} (hd : 0 < d) (ℱ : Filtration ℕ mΩ)
    (μ : Fin d → ℝ) (I : ℕ → Ω → Fin d) (η : ℕ → Ω → ℝ)
    (hI : ∀ t : ℕ, Measurable[ℱ t] (I (t + 1)))
    (hη : ∀ t : ℕ, Measurable[ℱ (t + 1)] (η (t + 1)))
    (hsg : ∀ t : ℕ, HasCondSubgaussianMGF (ℱ t) (ℱ.le t) (η (t + 1)) 1 P)
    {δ : ℝ} (hδ : 0 < δ) (hrun : IsUCBDeltaRun d δ μ η I) :
    P {ω | ∃ n : ℕ,
        ∑ i ∈ Finset.univ.filter (fun i => 0 < gap μ i),
            (3 * gap μ i + 16 / gap μ i * Real.log (2 * (d : ℝ) / (gap μ i * δ)))
          < pseudoRegret μ I n ω}
      ≤ ENNReal.ofReal δ := by sorry

end ImprovedLinBandits.UCBDelta
