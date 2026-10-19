-- Prove2me | Theorems.Thm_OAI_RadialTransition_corePressure_uniform_bare
-- name    : OAI.RadialTransition.corePressure_uniform_bare
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T01:05:00.473218+00:00
-- url     : https://prove2.me/theorems/a2349d78-199e-4d4f-aa0b-5e2e466a8028
-- title:
--   The grand pressure of the bounded core potential converges to the bare packing limit, uniformly for β ≥ β₀ and |h| ≤ H (OpenAI, radial phase transition)
-- statement:
--   Let $\beta_0 > 0$, $H \ge 0$ and $\varepsilon > 0$ (`hβ₀`, `hH`, `hε`). Then for all sufficiently large $t$, and for all $\beta \ge \beta_0$ and $|h| \le H$,
--   $$\bigl|\,P_t(\beta, h) - \mathrm{bare}(h)\,\bigr| \le \varepsilon .$$
--   The two quantities are:
--   - $P_t$ = `grandPressure (corePotential t) t` is the grand pressure of the bounded core potential `corePotential t`. That potential equals $t^2$ inside a core of radius about $e^{-t}$ and drops to $0$ across two thin shells.
--   - $\mathrm{bare}(h)$ = `bareLimit h` $= \max\bigl(0,\ p\,h,\ p(4h-9)\bigr)$, where $p$ is the sphere-packing density `packingDensity`.
--
--   `grandPressure`, `corePotential`, `bareLimit` and `packingDensity` come from the definitions bundle `OAIQWRTD000` of this split. The carver publishes this lemma as an intermediate statement so that each proof fits the platform's verifier.
--
--   Lean: `OAI.RadialTransition.corePressure_uniform_bare`, OpenAI's lemma of that name in `lean/OAI/Probability/RadialTransition/CoreConvergence.lean`.
-- source:
--   OpenAI, A radial continuum phase transition with algebraic decay, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 228; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-radial-continuum-phase-transition-with-algebraic-decay-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/RadialTransition/CoreConvergence.lean (declaration OAI.RadialTransition.corePressure_uniform_bare)

import Mathlib
import Definitions.Def_OAIQWRTD000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators ENNReal NNReal
open MeasureTheory Set Filter
namespace RadialTransition

lemma corePressure_uniform_bare {β₀ H ε : ℝ} (hβ₀ : 0 < β₀) (hH : 0 ≤ H) (hε : 0 < ε) :
    ∀ᶠ t : ℝ in atTop, ∀ β h : ℝ, β₀ ≤ β → |h| ≤ H →
      |grandPressure (corePotential t) t β h-bareLimit h| ≤ ε := by
  sorry

end RadialTransition
end

end OAI
end
