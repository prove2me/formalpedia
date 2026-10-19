-- Prove2me | Theorems.Thm_OAI_ZeroTemperatureSK_Heat_gaussian_heat_equation
-- name    : OAI.ZeroTemperatureSK.Heat.gaussian_heat_equation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T00:27:39.017623+00:00
-- url     : https://prove2.me/theorems/d7e0c39a-886d-4efe-9e1a-51f7b7d84928
-- title:
--   The Gaussian smoothing u(t,x) = E[g(x + √t Z)] solves the heat equation ∂ₜu = ½∂ₓ²u for C² data of exponential growth
-- statement:
--   Let $g : \mathbb R \to \mathbb R$ be twice continuously differentiable (`ContDiff ℝ 2 g`). Suppose that $g$, its derivative $g'$ (`deriv g`) and its second derivative $g''$ (`deriv (deriv g)`) each have at most exponential growth: for each $h \in \{g, g', g''\}$ there are $A, K \ge 0$ (`ℝ≥0`) with $|h(z)| \le A\,e^{K|z|}$ for all $z \in \mathbb R$.
--
--   For $s \ge 0$ and $x \in \mathbb R$ let
--   $$u(s, x) = \int g\bigl(x + \sqrt{s}\,y\bigr)\,d\gamma(y),$$
--   where $\gamma$ is the standard Gaussian measure on $\mathbb R$ (`gaussianReal 0 1`) and $\sqrt{\cdot}$ is `Real.sqrt`. Let $t \ge 0$ and $x \in \mathbb R$. Then the function $s \mapsto u(s, x)$ has derivative
--   $$\tfrac12\,\partial_x^2 u(t, x)$$
--   at $s = t$ within $[0, \infty)$ (`HasDerivWithinAt … (Set.Ici 0) t`). Here $\partial_x^2 u(t, x)$ is `deriv (deriv (fun z => u t z)) x`, Mathlib's iterated one-variable derivative.
--
--   Lean: `OAI.ZeroTemperatureSK.Heat.gaussian_heat_equation`. It uses only Mathlib. OpenAI's lemma `varianceHeat_equation` states the same with `varianceHeat t g x` for $u(t, x)$ (through `scaled`) and `ExponentialBound` for the growth conditions; this statement unfolds those definitions.
-- source:
--   Classical (heat equation for the Gauss–Weierstrass kernel). Proof: OpenAI, Full support of the zero-temperature Sherrington-Kirkpatrick order parameter, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 281, commit adc7f12, Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Foundations/ExponentialBoundLipschitz.lean (OpenAI's lemma OAI.ZeroTemperatureSK.Heat.varianceHeat_equation, restated with its definitions unfolded)

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

theorem gaussian_heat_equation {g : ℝ → ℝ} (hgc : ContDiff ℝ 2 g)
    (hg : ∃ A K : ℝ≥0, ∀ z, |g z| ≤ (A:ℝ)*Real.exp ((K:ℝ)*|z|))
    (hg' : ∃ A K : ℝ≥0, ∀ z, |deriv g z| ≤ (A:ℝ)*Real.exp ((K:ℝ)*|z|))
    (hg'' : ∃ A K : ℝ≥0, ∀ z, |deriv (deriv g) z| ≤ (A:ℝ)*Real.exp ((K:ℝ)*|z|))
    {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    HasDerivWithinAt (fun s => ∫ y, g (x + Real.sqrt s * y) ∂gaussianReal 0 1)
      ((1/2:ℝ) * deriv (deriv (fun z => ∫ y, g (z + Real.sqrt t * y) ∂gaussianReal 0 1)) x)
      (Set.Ici 0) t := by
  sorry

end ZeroTemperatureSK.Heat

end
end
end
end

end OAI
end
