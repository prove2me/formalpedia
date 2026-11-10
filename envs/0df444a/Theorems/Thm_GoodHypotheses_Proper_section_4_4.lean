-- Prove2me | Theorems.Thm_GoodHypotheses_Proper_section_4_4
-- name    : GoodHypotheses.Proper.section_4_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:15:53.925928+00:00
-- url     : https://prove2.me/theorems/a0159362-2720-4469-b9f4-7f0689590fa2
-- title:
--   §4.4 — the score estimator is unbiased: E_{X∼h_mix}[σ̂_i] = d_TV(h_i, ρ)
-- statement:
--   Let $h_1,\dots,h_n$ be probability densities, $\tilde W$ normalized weights, $h_{mix}=\sum_j\tilde W_jh_j$, and $\rho$ the proxy, with $\rho\le C\,h_{mix}$. For $X\sim h_{mix}$ and $r=\rho/h_{mix}$, the score estimator
--   $$\hat\sigma_i=\frac{1+r(X)}2-\frac{\min\{h_i(X),\rho(X)\}}{h_{mix}(X)}$$
--   satisfies $\mathbb E_{X\sim h_{mix}}[\hat\sigma_i]=d_{TV}(h_i,\rho)$. These are the auxiliary statistics of Theorem 3.5 in the proof of Theorem 1.1.
--
--   Differences from the source:
--
--   - generalization: ρ^t the weighted median of the h_i → any nonnegative μ-integrable ρ with ρ ≤ C·h_mix for some real C; reason: the weighted median is such a ρ: it is nonnegative and measurable (pointwise one of the h_i(x), chosen by finitely many measurable comparisons) and ρ ≤ 2h_mix (Lemma 4.1), hence integrable
--   - encoding: X^t ∼ h^t_mix → X drawn from a ProbabilityMeasure Pmix with Pmix = h_mix·μ; reason: Lean represents a draw by its law
--   - encoding: E[·] = value → the score estimator is integrable under Pmix and its integral equals dTV(h_i, ρ); reason: Lean's integral of a non-integrable function is 0; the paper's expectation exists
--   - encoding: normalized weights W̃ (W̃_i = W_i / ∑_j W_j) → any W with W_i ≥ 0 and ∑_i W_i = 1; reason: the paper uses exactly these properties (p. 21: "any non-negative values summing to one"); normalized MWU weights are such
--   - encoding: items i ∈ [n] = {1, …, n} → i : Fin n (0-based); reason: Lean convention; same instances
-- source:
--   Aamand, Aliakbarpour, Chen, Silwal, Stevens, Zou, A Good Way to Find Good Hypotheses, STOC 2027 submission (manuscript sha256 a428fbe0…), pp. 21–22, §4.4

import Mathlib
import Definitions.Def_GoodHypotheses_Proper_Proxies

open MeasureTheory

namespace GoodHypotheses.Proper

/-- §4.4 (pp. 21–22): let `h_1, …, h_n` be probability densities, `W̃` normalized weights
(nonnegative, summing to `1`), `h_mix = ∑_j W̃_j h_j` the density of the law `Pmix`, and `ρ` a
nonnegative integrable proxy with `ρ ≤ C h_mix` (for the weighted median, `C = 2` by
Lemma 4.1). For `X ∼ Pmix` and `r = ρ/h_mix`, the score estimator
`σ̂_i = (1 + r(X))/2 − min{h_i(X), ρ(X)}/h_mix(X)` is integrable and `E[σ̂_i] = dTV(h_i, ρ)`. -/
theorem section_4_4 {X : Type*} [MeasurableSpace X] (μ : Measure X) {n : ℕ}
    (h : Fin n → X → ℝ) (W : Fin n → ℝ) (ρ : X → ℝ) (Pmix : ProbabilityMeasure X) (C : ℝ)
    (i : Fin n) (hh : ∀ j, IsProbDensity μ (h j)) (hW0 : ∀ j, 0 ≤ W j) (hW1 : ∑ j, W j = 1)
    (hmix : IsDensityOf μ Pmix (mixture h W))
    (hρ0 : ∀ x, 0 ≤ ρ x) (hρ : Integrable ρ μ) (hρC : ∀ x, ρ x ≤ C * mixture h W x) :
    Integrable (fun x => scoreEstimate (h i) ρ (mixture h W) x) (Pmix : Measure X) ∧
      ∫ x, scoreEstimate (h i) ρ (mixture h W) x ∂(Pmix : Measure X) = tvDist μ (h i) ρ := by sorry

end GoodHypotheses.Proper
