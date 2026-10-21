-- Prove2me | Theorems.Thm_LeviSampling_BaseStock_stage_alpha_point
-- name    : LeviSampling.BaseStock.stage_alpha_point
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-20T15:50:27.933922+00:00
-- url     : https://prove2.me/theorems/9ab6e8ac-a50d-4e05-af3f-af53c16ce006
-- title:
--   Lemma 3.5 — one stage of the algorithm yields an α-point above R̄ with probability 1 − δ
-- statement:
--   Consider the multiperiod model with independent demands of finite mean and constant costs $h, b > 0$, periods $0$-based, $t < T$. Fix deterministic levels $L_{t+1}, \dots, L_{T-1}$ forming an upper base-stock policy and let $\bar R_t$ be the smallest minimizer of $\tilde U_t$. Let $0 < \alpha_t \le 2h(T-t)$, $0 < \delta_t < 1$, and draw $N$ independent sample paths of the demands with
--   $$N \ge 2\big((b+h)(T-t)\big)^2 \frac{1}{\alpha_t^2}\log\frac{2}{\delta_t}.$$
--   Let $\tilde R_t = \inf\{y : \hat U^r_t(y) \ge \alpha_t/2\}$. Then with probability at least $1 - \delta_t$,
--   $$\tilde R_t \text{ is an } \alpha_t\text{-point of } \tilde U_t \quad\text{and}\quad \tilde R_t \ge \bar R_t .$$
--
--   **Formalization Note** The paper's $T - t + 1$ is $T - t$ with $0$-based $t$. The condition $\alpha_t \le 2h(T-t)$ is the paper's well-definedness condition for $\tilde R_t$ (p. 835, just before Theorem 3.4). The probability is the product law of $N$ independent paths; on non-measurable events it is an outer measure.
-- source:
--   Levi, Roundy & Shmoys, Provably Near-Optimal Sampling-Based Policies for Stochastic Inventory Control Models, Math. Oper. Res. 32(4) 2007, p. 835, Lemma 3.5

import Mathlib
import Definitions.Def_LeviSampling_BaseStock_Shadow
import Definitions.Def_LeviSampling_BaseStock_Estimator
import Definitions.Def_LeviSampling_BaseStock_AlphaPoint

open MeasureTheory

namespace LeviSampling.BaseStock

/-- **Lemma 3.5** (Levi, Roundy & Shmoys 2007, p. 835), 0-based periods, constant costs
`h, b > 0`. Fix levels `L_{t+1}, …, L_{T-1}` forming an upper base-stock policy, and let `R̄_t` be
the smallest minimizer of `Ũ_t`. Let `0 < α_t ≤ 2h(T - t)` and `0 < δ_t < 1`, and draw
`N ≥ 2((b + h)(T - t))² (1/α_t²) log(2/δ_t)` independent sample paths of the demands. Then, with
probability at least `1 - δ_t`, the level `R̃_t = inf {y : Û^r_t(y) ≥ α_t/2}` is an `α_t`-point of
`Ũ_t` and `R̃_t ≥ R̄_t`. -/
theorem stage_alpha_point (T : ℕ) (μ : ℕ → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, Integrable id (μ i)) (h b : ℝ) (hh : 0 < h) (hb : 0 < b)
    (L : ℕ → ℝ) (t : ℕ) (ht : t < T)
    (hL : IsUpperBaseStock T μ (fun _ => h) (fun _ => b) L (t + 1))
    (Rbar : ℝ) (hRbar : IsSmallestMinimizer (shadowU T μ (fun _ => h) (fun _ => b) L t) Rbar)
    (α δt : ℝ) (hα : 0 < α) (hαh : α ≤ 2 * h * ((T - t : ℕ) : ℝ)) (hδ : 0 < δt) (hδ1 : δt < 1)
    (N : ℕ)
    (hN : 2 * ((b + h) * ((T - t : ℕ) : ℝ)) ^ 2 * (1 / α ^ 2) * Real.log (2 / δt) ≤ N) :
    ENNReal.ofReal (1 - δt) ≤
      (Measure.pi fun _ : Fin N => pathLaw T μ)
        {paths | IsAlphaPoint (shadowU T μ (fun _ => h) (fun _ => b) L t) α
              (sInf {y | α / 2 ≤ sampleRightDeriv T (fun _ => h) (fun _ => b) L t paths y}) ∧
            Rbar ≤ sInf {y | α / 2 ≤ sampleRightDeriv T (fun _ => h) (fun _ => b) L t paths y}} := by sorry

end LeviSampling.BaseStock
