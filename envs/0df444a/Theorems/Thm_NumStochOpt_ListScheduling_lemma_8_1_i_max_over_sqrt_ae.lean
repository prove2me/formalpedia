-- Prove2me | Theorems.Thm_NumStochOpt_ListScheduling_lemma_8_1_i_max_over_sqrt_ae
-- name    : NumStochOpt.ListScheduling.lemma_8_1_i_max_over_sqrt_ae
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-30T21:03:02.574041+00:00
-- url     : https://prove2.me/theorems/e5297738-a819-45a7-85b8-85b0b65fb32e
-- title:
--   Lemma 8.1 (i) — $p_{\max}/\sqrt n \to 0$ almost surely when $\mathbb E p_1^2 < \infty$
-- statement:
--   Let $p_1, p_2, \dots$ be independent, identically distributed, nonnegative random variables on a probability space $(\Omega, \mathcal F, P)$ with $\mathbb E p_1^2 < \infty$, and let $p_{\max}^{(n)} = \max_{j=1,\dots,n} p_j$. Then
--
--   $$
--   \lim_{n\to\infty} \frac{p_{\max}^{(n)}}{\sqrt n} = 0 \quad \text{almost surely.}
--   $$
--
--   The largest of $n$ processing times grows more slowly than $\sqrt n$; with $m = O(\sqrt n)$ machines this makes the list-scheduling error term $m\,p_{\max}/(n\mu)$ of (8.10) vanish.
--
--   The book states this lemma without proof and refers to Feller.
--
--   **Formalization Note** The sequence is `p : ℕ → Ω → ℝ` (0-based), mutually independent (`iIndepFun`), each `p j` measurable and identically distributed with `p 0`, pointwise nonnegative. $\mathbb E p_1^2 < \infty$ is integrability of `p 0 ^ 2`. Nonnegativity is the book's standing assumption on processing times.
-- source:
--   A. H. G. Rinnooy Kan, L. Stougie, "Stochastic Integer Programming", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 8, p. 206, Lemma 8.1 (i) (model: p. 205)

import Mathlib
import Definitions.Def_NumStochOpt_ListScheduling_Makespan

open MeasureTheory ProbabilityTheory Filter Topology

namespace NumStochOpt.ListScheduling

/-- Lemma 8.1 (i), p. 206: if the processing times `p 0, p 1, …` are i.i.d., nonnegative, with
`E p₁² < ∞`, then `p_max / √n → 0` almost surely, `p_max = max_{j<n} p j`. -/
theorem lemma_8_1_i_max_over_sqrt_ae {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (p : ℕ → Ω → ℝ) (hmeas : ∀ j, Measurable (p j))
    (hindep : iIndepFun p P) (hident : ∀ j, IdentDistrib (p j) (p 0) P P)
    (hnonneg : ∀ j ω, 0 ≤ p j ω) (hsq : Integrable (fun ω => p 0 ω ^ 2) P) :
    ∀ᵐ ω ∂P, Tendsto (fun n : ℕ => maxProcTime n (fun j => p j ω) / Real.sqrt n)
      atTop (𝓝 0) := by sorry

end NumStochOpt.ListScheduling
