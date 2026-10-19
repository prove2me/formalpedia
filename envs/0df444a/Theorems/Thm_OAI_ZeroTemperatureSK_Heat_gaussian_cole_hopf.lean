-- Prove2me | Theorems.Thm_OAI_ZeroTemperatureSK_Heat_gaussian_cole_hopf
-- name    : OAI.ZeroTemperatureSK.Heat.gaussian_cole_hopf
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T00:27:38.201792+00:00
-- url     : https://prove2.me/theorems/8e086ed1-9e1f-46dd-ab6a-5bd7d40a33af
-- title:
--   Cole–Hopf: (1/c) log of the Gaussian smoothing of g solves ∂ₜw = ½∂ₓ²w + (c/2)(∂ₓw)² (viscous Hamilton–Jacobi equation)
-- statement:
--   Let $g : \mathbb R \to \mathbb R$ be twice continuously differentiable (`ContDiff ℝ 2 g`). Suppose that $g$, its derivative $g'$ (`deriv g`) and its second derivative $g''$ (`deriv (deriv g)`) each have at most exponential growth: for each $h \in \{g, g', g''\}$ there are $A, K \ge 0$ (`ℝ≥0`) with $|h(z)| \le A\,e^{K|z|}$ for all $z \in \mathbb R$.
--
--   For $s \ge 0$ and $x \in \mathbb R$ let
--   $$u(s, x) = \int g\bigl(x + \sqrt{s}\,y\bigr)\,d\gamma(y),$$
--   where $\gamma$ is the standard Gaussian measure on $\mathbb R$ (`gaussianReal 0 1`) and $\sqrt{\cdot}$ is `Real.sqrt`. Let $c \ne 0$ and $t \ge 0$ be real numbers, and assume $u(t, z) > 0$ for every $z \in \mathbb R$. Let $w(s, z) = \log(u(s, z))/c$ (`Real.log`). Then for every $x \in \mathbb R$, the function $s \mapsto w(s, x)$ has derivative
--   $$\tfrac12\,\partial_x^2 w(t, x) + \tfrac{c}{2}\,\bigl(\partial_x w(t, x)\bigr)^2$$
--   at $s = t$ within $[0, \infty)$ (`HasDerivWithinAt … (Set.Ici 0) t`). Here $\partial_x w(t, x)$ is `deriv (fun z => w t z) x` and $\partial_x^2 w(t, x)$ is `deriv (deriv (fun z => w t z)) x`, Mathlib's one-variable derivatives.
--
--   Lean: `OAI.ZeroTemperatureSK.Heat.gaussian_cole_hopf`. It uses only Mathlib. OpenAI's lemma `logarithmic_heat_equation` states the same with `varianceHeat t g z` for $u(t, z)$ (through `scaled`) and `ExponentialBound` for the growth conditions; this statement unfolds those definitions.
-- source:
--   Cole–Hopf transformation (E. Hopf, The partial differential equation uₜ + uuₓ = μuₓₓ, Communications on Pure and Applied Mathematics 3 (1950), 201–230; J. D. Cole, On a quasi-linear parabolic equation occurring in aerodynamics, Quarterly of Applied Mathematics 9 (1951), 225–236). Proof: OpenAI, Full support of the zero-temperature Sherrington-Kirkpatrick order parameter, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 281, commit adc7f12, Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Foundations/ExponentialBoundLipschitz.lean (OpenAI's lemma OAI.ZeroTemperatureSK.Heat.logarithmic_heat_equation, restated with its definitions unfolded)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal Topology ContDiff
noncomputable section

namespace ZeroTemperatureSK.Heat

theorem gaussian_cole_hopf {g : ℝ → ℝ} (hgc : ContDiff ℝ 2 g)
    (hg : ∃ A K : ℝ≥0, ∀ z, |g z| ≤ (A:ℝ)*Real.exp ((K:ℝ)*|z|))
    (hg' : ∃ A K : ℝ≥0, ∀ z, |deriv g z| ≤ (A:ℝ)*Real.exp ((K:ℝ)*|z|))
    (hg'' : ∃ A K : ℝ≥0, ∀ z, |deriv (deriv g) z| ≤ (A:ℝ)*Real.exp ((K:ℝ)*|z|))
    {c : ℝ} (hc : c ≠ 0) {t : ℝ} (ht : 0 ≤ t)
    (hpos : ∀ z, 0 < ∫ y, g (z + Real.sqrt t * y) ∂gaussianReal 0 1) (x : ℝ) :
    HasDerivWithinAt
      (fun s => Real.log (∫ y, g (x + Real.sqrt s * y) ∂gaussianReal 0 1) / c)
      ((1/2:ℝ) * deriv (deriv (fun z =>
          Real.log (∫ y, g (z + Real.sqrt t * y) ∂gaussianReal 0 1) / c)) x +
        c/2 * (deriv (fun z =>
          Real.log (∫ y, g (z + Real.sqrt t * y) ∂gaussianReal 0 1) / c) x)^2)
      (Set.Ici 0) t := by
  sorry

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI
end
