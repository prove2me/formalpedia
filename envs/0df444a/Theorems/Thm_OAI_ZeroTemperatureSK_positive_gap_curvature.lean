-- Prove2me | Theorems.Thm_OAI_ZeroTemperatureSK_positive_gap_curvature
-- name    : OAI.ZeroTemperatureSK.positive_gap_curvature
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T00:34:11.17036+00:00
-- url     : https://prove2.me/theorems/cbe4d178-ea2a-4afa-baed-b89df8166175
-- title:
--   On an interval where the order parameter is a positive constant, the curvature moment of the optimal diffusion is strictly convex (OpenAI zero-temperature SK)
-- statement:
--   Definitions from the published bundle `Def_SKFullSupport`: `Time` is $[0, 1)$, and `extend γ` extends a function on `Time` by $0$ to $\mathbb R$. An `OrderParameter` is a function $\gamma$ on `Time` (`val`) that is nonnegative, monotone, right-continuous, and whose extension is integrable. A `BrownianSystem Ω` is a probability measure (`law`) on a measurable space $\Omega$ carrying a real Brownian motion $B$ (`IsBrownianReal`). A `Control W t` is a process adapted to the increments of $B$ after time $t$, progressively measurable, with values in $[-1, 1]$. The payoff of a control $\alpha$ from $(t, x)$ is
--   $$\Bigl|x + B_1 - B_t + \int_t^1 \gamma(s)\,\alpha_{s-t}\,ds\Bigr| - \tfrac12\int_t^1 \gamma(s)\,\alpha_{s-t}^2\,ds$$
--   (`controlPayoff`). `value W γ t x` is the supremum over controls of its expectation, and `gradient` and `curvature` are its first and second derivatives in $x$ (Mathlib's `deriv`).
--
--   Definitions from the definitions bundles of this split: `diffusion W γ` is OpenAI's construction of the associated optimal diffusion, $t \mapsto$ `W.driver t ω` $+ \int_0^t \gamma(s)\,$`rawFeedback W γ s ω`$\,ds$. The curvature moment is
--   $$\mathrm{curvatureMoment}\ W\ \gamma\ t = \int \bigl(\mathrm{curvature}\ W\ \gamma\ t\ (\mathrm{diffusion}\ W\ \gamma\ t\ \omega)\bigr)^2\,d\,\mathrm{law}(\omega)$$
--   (with $t$ cast to $[0, \infty)$ by `Real.toNNReal`).
--
--   Let $W$ be a `BrownianSystem Ω` and $\gamma$ an `OrderParameter`. Let $a, b, c$ be real numbers with $0 \le a < b < 1$ and $c > 0$, and suppose `extend γ.val s` $= c$ for every $s \in (a, b)$. Then for every $t \in (a, b)$ the second derivative of $t \mapsto \mathrm{curvatureMoment}\ W\ \gamma\ t$ at $t$ is positive (`(deriv^[2] (curvatureMoment W γ)) t > 0`).
--
--   Lean: `OAI.ZeroTemperatureSK.positive_gap_curvature`, OpenAI's theorem of that name (in `lean/OAI/Probability/SKSupport/Support/GapCurvature.lean`). `extend`, `OrderParameter`, `BrownianSystem`, `Control`, `controlPayoff`, `value`, `gradient` and `curvature` come from the published bundle `Def_SKFullSupport`; `diffusion`, `rawFeedback` and `curvatureMoment` from the definitions bundles of this split.
-- source:
--   OpenAI, Full support of the zero-temperature Sherrington-Kirkpatrick order parameter, OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 281; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SKSupport/Support/GapCurvature.lean (declaration OAI.ZeroTemperatureSK.positive_gap_curvature)

import Mathlib
import Definitions.Def_SKFullSupport
import Definitions.Def_OAIQWZT002

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
namespace ZeroTemperatureSK
open Heat WeakIto
variable {Ω : Type*} [MeasurableSpace Ω]

theorem positive_gap_curvature (W : BrownianSystem Ω) (γ : OrderParameter)
    {a b c : ℝ} (ha : 0 ≤ a) (hab : a < b) (hb : b < 1) (hc0 : 0 < c)
    (hc : ∀ s ∈ Ioo a b, extend γ.val s=c) :
    ∀ t ∈ Ioo a b, 0 < (deriv^[2] (curvatureMoment W γ)) t := by
  sorry

end ZeroTemperatureSK

end
end

end OAI
end
