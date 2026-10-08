-- Prove2me | Theorems.Thm_OptimalRLS_Upper_proposition_2
-- name    : OptimalRLS.Upper.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T19:04:01.111618+00:00
-- url     : https://prove2.me/theorems/9ff4bdbc-0744-4eeb-b863-df42186586ee
-- title:
--   Proposition 2, p. 13 — Bernstein inequality for i.i.d. means in a separable Hilbert space under the moment condition (31)
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space and $\xi$ an integrable random variable on $\Omega$ with values in a real separable Hilbert space $\mathcal K$. Let $L,\sigma>0$.
--
--   1. If
--   $$\mathbb E\big[\|\xi-\mathbb E[\xi]\|_{\mathcal K}^m\big]\le\tfrac12\,m!\,\sigma^2L^{m-2}\qquad\text{for all }m\ge2,\tag{31}$$
--   then for every $\ell\ge1$ and $0<\eta<1$,
--   $$P^\ell\Big[\Big\|\frac1\ell\sum_{i=1}^\ell\xi(\omega_i)-\mathbb E[\xi]\Big\|_{\mathcal K}\le2\Big(\frac L\ell+\frac\sigma{\sqrt\ell}\Big)\log\frac2\eta\Big]\ge1-\eta.\tag{32}$$
--   2. Condition (31) holds whenever $\|\xi\|_{\mathcal K}\le L/2$ almost surely and $\mathbb E[\|\xi\|_{\mathcal K}^2]\le\sigma^2$ (33).
--
--   This concentration inequality is applied three times in the proof of Theorem 4, to the Hilbert–Schmidt-valued variable $T_x$ and to two $\mathcal H$-valued variables.
--
--   **Formalization Note** (32) is stated in the equivalent form "the complementary event, where the norm exceeds the bound, has $P^\ell$-measure at most $\eta$", with $P^\ell$ the product measure on $\Omega^\ell$. The moments in (31) and (33) are integrals of nonnegative functions with values in $[0,\infty]$. $\xi$ is assumed measurable and Bochner integrable so that $\mathbb E[\xi]$ exists, which the paper takes for granted.
-- source:
--   Caponnetto & De Vito, Found. Comput. Math. 7 (2007), authors' copy, Proposition 2, (31)–(33), p. 13

import Mathlib

open MeasureTheory ProbabilityTheory

namespace OptimalRLS.Upper

/-- **Proposition 2** (p. 13). Let `(Ω, P)` be a probability space and `ξ` a measurable, integrable
random variable with values in a real separable Hilbert space `K`, and `L, σ > 0`.
(1) If (31) `E[‖ξ − E ξ‖^m] ≤ ½ m! σ² L^{m−2}` for all `m ≥ 2`, then for every `ℓ ≥ 1` and
`0 < η < 1`, the event `‖(1/ℓ) ∑ ξ(ω_i) − E ξ‖ > 2 (L/ℓ + σ/√ℓ) log(2/η)` has `P^ℓ`-probability at
most `η` (the complement of the event in (32)).
(2) (31) holds if (33): `‖ξ‖ ≤ L/2` almost surely and `E[‖ξ‖²] ≤ σ²`.
Moments are `lintegral`s of nonnegative integrands. -/
theorem proposition_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
    [TopologicalSpace.SeparableSpace K] [MeasurableSpace K] [BorelSpace K]
    (ξ : Ω → K) (hξm : Measurable ξ) (hξi : Integrable ξ P) (L σ : ℝ) (hL : 0 < L) (hσ : 0 < σ) :
    ((∀ m : ℕ, 2 ≤ m → ∫⁻ ω, ENNReal.ofReal (‖ξ ω - ∫ a, ξ a ∂P‖ ^ m) ∂P ≤
        ENNReal.ofReal ((m.factorial : ℝ) / 2 * σ ^ 2 * L ^ (m - 2))) →
      ∀ ℓ : ℕ, 1 ≤ ℓ → ∀ η : ℝ, 0 < η → η < 1 →
        (Measure.pi fun _ : Fin ℓ => P)
            {ω | 2 * (L / (ℓ : ℝ) + σ / Real.sqrt (ℓ : ℝ)) * Real.log (2 / η) <
              ‖(1 / (ℓ : ℝ)) • ∑ i, ξ (ω i) - ∫ a, ξ a ∂P‖} ≤ ENNReal.ofReal η) ∧
    (((∀ᵐ ω ∂P, ‖ξ ω‖ ≤ L / 2) ∧
        ∫⁻ ω, ENNReal.ofReal (‖ξ ω‖ ^ 2) ∂P ≤ ENNReal.ofReal (σ ^ 2)) →
      ∀ m : ℕ, 2 ≤ m → ∫⁻ ω, ENNReal.ofReal (‖ξ ω - ∫ a, ξ a ∂P‖ ^ m) ∂P ≤
        ENNReal.ofReal ((m.factorial : ℝ) / 2 * σ ^ 2 * L ^ (m - 2))) := by sorry

end OptimalRLS.Upper
