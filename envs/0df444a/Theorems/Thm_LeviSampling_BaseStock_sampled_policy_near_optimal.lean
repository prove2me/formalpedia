-- Prove2me | Theorems.Thm_LeviSampling_BaseStock_sampled_policy_near_optimal
-- name    : LeviSampling.BaseStock.sampled_policy_near_optimal
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:50:12.638014+00:00
-- url     : https://prove2.me/theorems/f7d23b91-1fbd-4e7c-b493-212aaa2e9648
-- title:
--   Theorem 3.5 (§3.3) — the sampled base-stock policy is (1 + ε)-optimal with probability 1 − δ
-- statement:
--   Consider the $T$-period ($T \ge 1$) backlogging inventory model with independent demands $D_0, \dots, D_{T-1}$ of arbitrary laws with finite mean, zero lead time, no ordering cost, and constant holding and backlogging costs $h, b > 0$. Fix an accuracy $0 < \varepsilon \le 1$ and a confidence $0 < \delta < 1$, and run the algorithm of §3.3: in stages $t = T-1, \dots, 0$ draw $N_t = \lceil 2((b+h)(T-t))^2\alpha_t^{-2}\log(2/\delta_t)\rceil$ fresh independent demand paths, with $\alpha_t = (\varepsilon/2T)/3\cdot\min(b,h)$ and $\delta_t = \delta/T$, and set $\tilde R_t = \inf\{y : \hat U^r_t(y) \ge \alpha_t/2\}$. Then
--   $$\Pr\Big[\ \tilde U_0(\tilde R_0) \le (1 + \varepsilon)\,\min_y U_0(y)\ \Big] \;\ge\; 1 - \delta,$$
--   where $\tilde U_0(\tilde R_0)$ is the expected cost of ordering up to $\tilde R_0$ in the first period and following $\tilde R_1, \dots, \tilde R_{T-1}$ afterwards, and $\min_y U_0(y)$ is the optimal expected cost of the dynamic program (1)–(2).
--
--   The sample sizes do not depend on the demand distributions; this is the first distribution-free sample-complexity guarantee for a multistage inventory model.
--
--   **Formalization Note** Periods are $0$-based (the paper's $\tilde R_1$ is $\tilde R_0$ here, and $T - t + 1$ becomes $T - t$). $N_t$ is rounded up. The probability is over the algorithm's product sample space and is an outer measure on non-measurable events.
-- source:
--   Levi, Roundy & Shmoys, Provably Near-Optimal Sampling-Based Policies for Stochastic Inventory Control Models, Math. Oper. Res. 32(4) 2007, p. 836, Theorem 3.5 (§3.3); algorithm on p. 835

import Mathlib
import Definitions.Def_LeviSampling_BaseStock_Shadow
import Definitions.Def_LeviSampling_BaseStock_Algorithm

open MeasureTheory

namespace LeviSampling.BaseStock

/-- **Theorem 3.5 (§3.3)** (Levi, Roundy & Shmoys 2007, p. 836), 0-based periods, constant costs
`h, b > 0`. For accuracy `0 < ε ≤ 1` and confidence `0 < δ < 1`, the base-stock levels
`R̃_0, …, R̃_{T-1}` computed by the algorithm of §3.3 (stage sizes
`N_t = ⌈2((b+h)(T-t))² (1/α_t²) log(2/δ_t)⌉`, `α_t = (ε/2T)/3 · min(b,h)`, `δ_t = δ/T`,
independent samples in every stage) satisfy, with probability at least `1 - δ`: the expected cost
`Ũ_0(R̃_0)` of ordering up to `R̃_0` in the first period and following `R̃_1, …, R̃_{T-1}`
afterwards is at most `(1 + ε)` times the optimal expected cost `min_y U_0(y)`. -/
theorem sampled_policy_near_optimal (T : ℕ) (hT : 1 ≤ T) (μ : ℕ → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (hμ : ∀ i, Integrable id (μ i))
    (h b : ℝ) (hh : 0 < h) (hb : 0 < b) (ε δ : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hδ : 0 < δ) (hδ1 : δ < 1) :
    ENNReal.ofReal (1 - δ) ≤
      algMeasure T μ h b ε δ
        {ω | shadowU T μ (fun _ => h) (fun _ => b) (algLevel T h b ε δ ω) 0
                (algLevel T h b ε δ ω 0) ≤
              (1 + ε) * optCost T μ (fun _ => h) (fun _ => b)} := by sorry

end LeviSampling.BaseStock
