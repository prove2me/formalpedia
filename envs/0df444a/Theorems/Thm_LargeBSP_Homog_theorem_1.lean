-- Prove2me | Theorems.Thm_LargeBSP_Homog_theorem_1
-- name    : LargeBSP.Homog.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:08:50.188952+00:00
-- url     : https://prove2.me/theorems/d3900ecf-b20d-43e0-b387-53d6f174d882
-- title:
--   Theorem 1, p. 11 — a single size ⌊Nt⋆⌋ priced at N V̄(t⋆) − g(N) is asymptotically optimal
-- statement:
--   Work in the large-offering regime (Assumptions 1–3: nonnegative valuations with $\mathbb F_{X,N}(y) \Rightarrow F_X(y)$, uniformly integrable with a weak law of large numbers toward the mean $\mu$ of $F_X$; bounded nonnegative costs with $\mathbb F_{C,N}(y) \to F_C(y)$). Assume there are nondecreasing continuous functions $\bar V, \bar c$ on $[0,1]$ with $\bar V_N(t) \Rightarrow \bar V(t)$ and $\bar c_N(t) \Rightarrow \bar c(t)$ for every $t \in [0,1]$, let $t^\star \in \arg\max_{t\in[0,1]} \bar V(t) - \bar c(t)$ with $\bar V(t^\star) - \bar c(t^\star) > 0$, and let
--   $$p_N(n) = \begin{cases} N\bar V(t^\star) - g(N) & n = \lfloor N t^\star \rfloor,\\ +\infty & n \ne \lfloor N t^\star \rfloor,\end{cases}$$
--   where $g(N) \in \omega_+\big(\sqrt{\mathbb E[(V_N(\lfloor Nt^\star\rfloor) - N\bar V(t^\star))^2]}\big) \cap o(N)$. Then $\{p_N\}$ is asymptotically optimal and
--   $$\lim_{N\to\infty} \frac{\mathbb E[\pi(p_N)]}{\mathbb E[\pi(p^\star)]} = \lim_{N\to\infty} \frac{\mathbb E[\pi(p_N)]}{N(\bar V(t^\star) - \bar c(t^\star))} = 1.$$
--
--   So, asymptotically, offering one bundle size is as good as the optimal BSP menu.
--
--   **Formalization Note** The conclusion is the two limits; the first is Definition 2's asymptotic optimality (10) of $\{p_N\}$. Two hypotheses are disclosed readings: continuity of $\bar V, \bar c$ (the theorem says "nondecreasing", the sentence introducing it on p. 11 says "nondecreasing and continuous", and the proof uses continuity) and $\bar V(t^\star) - \bar c(t^\star) > 0$ (the second ratio's denominator; otherwise the ratio is $0/0$). $\mathbb E[\pi(p^\star)]$ is the supremum over all BSP menus. Assumption 1 is a standing assumption of the regime that the proof does not use; it is kept as on the page. Prices $N\bar V(t^\star) - g(N)$ may be negative for finitely many $N$; only the limit matters.
-- source:
--   Abdallah, Asadpour & Reed, Large-Scale Bundle-Size Pricing: A Theoretical Analysis, author's manuscript (2021; Oper. Res. doi:10.1287/opre.2020.2097), Theorem 1, p. 11

import Mathlib
import Definitions.Def_LargeBSP_Homog_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace LargeBSP.Homog

/-- Theorem 1, p. 11: under the large-offering regime, if `V̄_N(t) ⇒ V̄(t)` and `c̄_N(t) ⇒ c̄(t)` for
every `t ∈ [0,1]` with nondecreasing continuous limits, `t⋆ = t₀ ∈ argmax V̄ − c̄` and
`g(N) ∈ ω₊(√E[(V_N(⌊Nt⋆⌋) − N V̄(t⋆))²]) ∩ o(N)`, the single-size menu `p_N` is asymptotically
optimal and `E[π(p_N)]/E[π(p⋆)] → 1`, `E[π(p_N)]/(N(V̄(t⋆) − c̄(t⋆))) → 1`. -/
theorem theorem_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
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
    (hmax : ∀ t ∈ Set.Icc (0 : ℝ) 1, Vl t - cl t ≤ Vl t₀ - cl t₀)
    (hpos : 0 < Vl t₀ - cl t₀)
    (g : ℕ → ℝ) (hg0 : ∀ᶠ N in atTop, 0 < g N)
    (hgo : Tendsto (fun N : ℕ => g N / N) atTop (𝓝 0))
    (hgω : Tendsto (fun N : ℕ =>
      (∫⁻ ω, ENNReal.ofReal ((V (fun n => X n ω) N ⌊(N : ℝ) * t₀⌋₊ - N * Vl t₀) ^ 2) ∂P) /
        ENNReal.ofReal (g N ^ 2)) atTop (𝓝 0)) :
    Tendsto (fun N : ℕ => expProfit P X c N (singleSizeMenu ⌊(N : ℝ) * t₀⌋₊ (N * Vl t₀ - g N)) / optProfit P X c N) atTop (𝓝 1) ∧
    Tendsto (fun N : ℕ => expProfit P X c N (singleSizeMenu ⌊(N : ℝ) * t₀⌋₊ (N * Vl t₀ - g N)) / (N * (Vl t₀ - cl t₀))) atTop (𝓝 1) := by sorry

end LargeBSP.Homog
