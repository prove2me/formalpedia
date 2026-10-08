-- Prove2me | Theorems.Thm_LinParamBandits_PEGE_small_mass_density
-- name    : LinParamBandits.PEGE.small_mass_density
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:21:27.227102+00:00
-- url     : https://prove2.me/theorems/a7a6ee87-c710-48d9-970e-bcb9fffe40c4
-- title:
--   Lemma 3.2(a) — a density of ‖Z‖ bounded by M₀x^ρ near 0 gives E[1/‖Z‖] ≤ M
-- statement:
--   Let $M_0 \in \mathbb R$ and $\rho \in (0, 1]$. There is a constant $M$, depending only on $M_0$ and $\rho$, with the following property. For every $r \ge 2$ and every probability law $\mu$ of $Z$ on $\mathbb R^r$ such that $\|Z\|$ has a density $g : \mathbb R_+ \to \mathbb R_+$ with $g(x) \le M_0 x^\rho$ for all $x \in [0, \rho]$,
--   $$\mathbb E\big[1/\|Z\|\big] \le M.$$
--
--   This gives a simple sufficient condition for the moment hypothesis of the risk bound in Theorem 3.1.
--
--   **Formalization Note** "$\|Z\|$ has density $g$" is written as: the image of $\mu$ under $z \mapsto \|z\|$ equals Lebesgue measure on $[0, \infty)$ with density $g$, for a measurable $g$ (measurability is implicit on the page). $\mathbb E[1/\|Z\|]$ is a lower Lebesgue integral with $1/0 = +\infty$.
-- source:
--   Rusmevichientong, Tsitsiklis, Linearly Parameterized Bandits, arXiv:0812.3465v2, Lemma 3.2(a), p. 16 (proof App. A.2, pp. 27–28)

import Mathlib
import Definitions.Def_LinParamBandits_PEGE_Model

open MeasureTheory ProbabilityTheory

namespace LinParamBandits.PEGE

/-- Lemma 3.2(a) (Small Mass Near the Origin), Rusmevichientong, Tsitsiklis,
arXiv:0812.3465v2, p. 16: if there are constants `M₀` and `ρ ∈ (0, 1]` such that for any `r ≥ 2`
the random variable `‖Z‖` has a density `g : ℝ₊ → ℝ₊` with `g(x) ≤ M₀ x^ρ` for all `x ∈ [0, ρ]`, then
`E[1/‖Z‖] ≤ M`, where `M` depends only on `M₀` and `ρ`. -/
theorem small_mass_density (M₀ ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) :
    ∃ M : ℝ, ∀ (r : ℕ), 2 ≤ r →
      ∀ (μ : Measure (LinParamBandits.LowerBound.Vec r)), IsProbabilityMeasure μ →
      ∀ (g : ℝ → NNReal), Measurable g →
        μ.map (fun z => ‖z‖) = (volume.restrict (Set.Ici (0 : ℝ))).withDensity (fun x => (g x : ENNReal)) →
        (∀ x ∈ Set.Icc (0 : ℝ) ρ, (g x : ℝ) ≤ M₀ * x ^ ρ) →
        ∫⁻ z, ‖z‖ₑ⁻¹ ∂μ ≤ ENNReal.ofReal M := by sorry
end LinParamBandits.PEGE
