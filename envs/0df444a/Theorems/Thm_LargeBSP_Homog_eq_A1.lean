-- Prove2me | Theorems.Thm_LargeBSP_Homog_eq_A1
-- name    : LargeBSP.Homog.eq_A1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:08:49.171804+00:00
-- url     : https://prove2.me/theorems/b48aa329-5f83-4137-84b9-e47bc7ea4f9d
-- title:
--   (A1), p. A1 — limsup E[π(p⋆)]/N ≤ V̄(t⋆) − c̄(t⋆)
-- statement:
--   Work in the large-offering regime: nonnegative valuations $X_1, X_2, \dots$ on a probability space with empirical cdfs $\mathbb F_{X,N}(y) \Rightarrow F_X(y)$ for $y \ge 0$ (Assumption 1), $\{X_n\}$ uniformly integrable with $\frac1N\sum_{n \le N} X_n \Rightarrow \mu$, the mean of $F_X$ (Assumption 2), and bounded nonnegative costs whose empirical cdf converges, $\mathbb F_{C,N}(y) \to F_C(y)$ for $y \ge 0$ (Assumption 3). Suppose further that there are nondecreasing continuous functions $\bar V, \bar c$ on $[0,1]$ with
--   $$\bar V_N(t) \Rightarrow \bar V(t), \qquad \bar c_N(t) \Rightarrow \bar c(t) \qquad (t \in [0,1]),$$
--   and let $t^\star \in \arg\max_{t \in [0,1]} \bar V(t) - \bar c(t)$. Then
--   $$\limsup_{N \to \infty} \frac{\mathbb E[\pi(p^\star)]}{N} \le \bar V(t^\star) - \bar c(t^\star),$$
--   where $\mathbb E[\pi(p^\star)]$ is the optimal expected BSP profit with $N$ products.
--
--   This is the upper half of Theorem 1.
--
--   **Formalization Note** "$\Rightarrow$" toward a deterministic limit is convergence in probability (`TendstoInMeasure`); the costs are deterministic, so Assumption 3 is ordinary convergence. The limsup bound is stated as "for every $\varepsilon > 0$, eventually $\mathbb E[\pi(p^\star)]/N \le \bar V(t^\star) - \bar c(t^\star) + \varepsilon$", which is equivalent and avoids `Filter.limsup` on $\mathbb R$. Continuity of $\bar V, \bar c$ comes from the sentence introducing Theorem 1 (p. 11) and is used by the proof; valuations are nonnegative and measurable.
-- source:
--   Abdallah, Asadpour & Reed, Large-Scale Bundle-Size Pricing: A Theoretical Analysis, author's manuscript (2021; Oper. Res. doi:10.1287/opre.2020.2097), proof of Theorem 1 (Appendix A.1), p. A1, (A1)

import Mathlib
import Definitions.Def_LargeBSP_Homog_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace LargeBSP.Homog

/-- (A1), p. A1: `limsup_{N→∞} E[π̄(p⋆)] ≤ V̄(t⋆) − c̄(t⋆)`, stated as: for every `ε > 0`,
eventually `E[π(p⋆)]/N ≤ V̄(t⋆) − c̄(t⋆) + ε`. Hypotheses: the large-offering regime
(Assumptions 1–3) and Theorem 1's limits `V̄`, `c̄` with maximizer `t⋆ = t₀`. -/
theorem eq_A1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℕ → Ω → ℝ) (hXm : ∀ n, Measurable (X n)) (hX0 : ∀ n ω, 0 ≤ X n ω)
    (ν : Measure ℝ) [IsProbabilityMeasure ν] (hν0 : ν (Set.Iio 0) = 0) (hν1 : Integrable id ν)
    (hA1 : ∀ y : ℝ, 0 ≤ y → TendstoInMeasure P
      (fun (N : ℕ) ω => empCdf (fun n => X n ω) N y) atTop (fun _ => cdf ν y))
    (hUI : UniformIntegrable X 1 P)
    (hWLLN : TendstoInMeasure P (fun (N : ℕ) ω => (∑ n ∈ Finset.range N, X n ω) / N) atTop
      (fun _ => ∫ y, y ∂ν))
    (c : ℕ → ℝ) (hc0 : ∀ n, 0 ≤ c n) (hcB : BddAbove (Set.range c))
    (νC : Measure ℝ) [IsProbabilityMeasure νC] (hνC0 : νC (Set.Iio 0) = 0) (hνC1 : Integrable id νC)
    (hA3 : ∀ y : ℝ, 0 ≤ y → Tendsto (fun N : ℕ => empCdf c N y) atTop (𝓝 (cdf νC y)))
    (Vl cl : ℝ → ℝ) (hVmono : MonotoneOn Vl (Set.Icc 0 1)) (hcmono : MonotoneOn cl (Set.Icc 0 1))
    (hVcont : ContinuousOn Vl (Set.Icc 0 1)) (hccont : ContinuousOn cl (Set.Icc 0 1))
    (hV : ∀ t ∈ Set.Icc (0 : ℝ) 1, TendstoInMeasure P
      (fun (N : ℕ) ω => Vbar (fun n => X n ω) N t) atTop (fun _ => Vl t))
    (hcv : ∀ t ∈ Set.Icc (0 : ℝ) 1, TendstoInMeasure P
      (fun (N : ℕ) ω => cbar c (fun n => X n ω) N t) atTop (fun _ => cl t))
    (t₀ : ℝ) (ht₀ : t₀ ∈ Set.Icc (0 : ℝ) 1)
    (hmax : ∀ t ∈ Set.Icc (0 : ℝ) 1, Vl t - cl t ≤ Vl t₀ - cl t₀) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop, optProfit P X c N / N ≤ Vl t₀ - cl t₀ + ε := by sorry

end LargeBSP.Homog
