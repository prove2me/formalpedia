-- Prove2me | Theorems.Thm_LargeBSP_Homog_eq_A5
-- name    : LargeBSP.Homog.eq_A5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:08:48.000142+00:00
-- url     : https://prove2.me/theorems/557d4cd5-d81e-4947-814b-5bb77df5f364
-- title:
--   (A5), p. A2 — liminf E[π(p_N)]/N ≥ V̄(t⋆) − c̄(t⋆) for the single-size menu p_N
-- statement:
--   Under the hypotheses of Theorem 1 except the positivity $\bar V(t^\star) > \bar c(t^\star)$ — the large-offering regime (Assumptions 1–3), nondecreasing continuous limits $\bar V_N(t) \Rightarrow \bar V(t)$, $\bar c_N(t) \Rightarrow \bar c(t)$ on $[0,1]$, a maximizer $t^\star$ of $\bar V - \bar c$ on $[0,1]$, and $g(N) \in \omega_+\big(\sqrt{\mathbb E[(V_N(\lfloor Nt^\star\rfloor) - N\bar V(t^\star))^2]}\big) \cap o(N)$ — let $p_N$ offer the single size $\lfloor Nt^\star \rfloor$ at price $N\bar V(t^\star) - g(N)$ (every other size at $+\infty$). Then
--   $$\liminf_{N \to \infty} \frac{\mathbb E[\pi(p_N)]}{N} \ge \bar V(t^\star) - \bar c(t^\star).$$
--
--   This is the lower half of Theorem 1.
--
--   **Formalization Note** Stated as "for every $\varepsilon > 0$, eventually $\bar V(t^\star) - \bar c(t^\star) - \varepsilon \le \mathbb E[\pi(p_N)]/N$". $g \in o(N)$ is $g(N)/N \to 0$ with $g$ eventually positive; the $\omega_+$ condition is encoded as in (A4). The page's intermediate display (A2) is not formalized (see the mission notes); (A5) is.
-- source:
--   Abdallah, Asadpour & Reed, Large-Scale Bundle-Size Pricing: A Theoretical Analysis, author's manuscript (2021; Oper. Res. doi:10.1287/opre.2020.2097), proof of Theorem 1 (Appendix A.1), p. A2, (A5)

import Mathlib
import Definitions.Def_LargeBSP_Homog_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace LargeBSP.Homog

/-- (A5), p. A2: `liminf_{N→∞} E[π̄(p_N)] ≥ V̄(t⋆) − c̄(t⋆)` for the single-size menu `p_N`
(size `⌊Nt⋆⌋` at price `N V̄(t⋆) − g(N)`), stated as: for every `ε > 0`, eventually
`V̄(t⋆) − c̄(t⋆) − ε ≤ E[π(p_N)]/N`. -/
theorem eq_A5 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
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
    (g : ℕ → ℝ) (hg0 : ∀ᶠ N in atTop, 0 < g N)
    (hgo : Tendsto (fun N : ℕ => g N / N) atTop (𝓝 0))
    (hgω : Tendsto (fun N : ℕ =>
      (∫⁻ ω, ENNReal.ofReal ((V (fun n => X n ω) N ⌊(N : ℝ) * t₀⌋₊ - N * Vl t₀) ^ 2) ∂P) /
        ENNReal.ofReal (g N ^ 2)) atTop (𝓝 0)) :
    ∀ ε > 0, ∀ᶠ N : ℕ in atTop,
      Vl t₀ - cl t₀ - ε ≤ expProfit P X c N (singleSizeMenu ⌊(N : ℝ) * t₀⌋₊ (N * Vl t₀ - g N)) / N := by sorry

end LargeBSP.Homog
