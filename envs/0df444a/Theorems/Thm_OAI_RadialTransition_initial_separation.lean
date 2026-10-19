-- Prove2me | Theorems.Thm_OAI_RadialTransition_initial_separation
-- name    : OAI.RadialTransition.initial_separation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T01:06:48.53499+00:00
-- url     : https://prove2.me/theorems/79fa6e2c-e784-43a5-9c2b-667789d70b4a
-- title:
--   The ideal attraction transform of the core pressure is near the three-phase plane and has three phase groups (OpenAI, radial phase transition)
-- statement:
--   Let $\tau > 0$ and $\varepsilon_0 > 0$. Then for all sufficiently large $t$, every parameter $x = (\beta, h)$ in `phaseWindow (1/4)` satisfies two conditions. Here $Q_t$ = `idealAttraction (grandPressure (corePotential t) t) phaseMass` is the ideal attraction transform, with mass `phaseMass` $= 3/(2p)$, of the core grand pressure.
--   1. $|Q_t(x) - \Pi(x)| \le \varepsilon_0$, where $\Pi$ = `threePlane` is the maximum of the three limiting affine pressures `limitingPlane i` of phases of densities $0$, $p$ and $4p$.
--   2. `HasPhaseGroups Q_t x (τ/2)` holds: the supporting slopes of $Q_t$ at $x$ (over $\beta > 0$) form the closed convex hull of those lying within $\tau/2$ of one of the three phase slopes.
--
--   The named functions come from the definitions bundle `OAIQWRTD000` of this split. The carver publishes this lemma as an intermediate statement so that each proof fits the platform's verifier.
--
--   Lean: `OAI.RadialTransition.initial_separation`, OpenAI's lemma of that name in `lean/OAI/Probability/RadialTransition/InitialSeparation.lean`.
-- source:
--   OpenAI, A radial continuum phase transition with algebraic decay, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 228; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-radial-continuum-phase-transition-with-algebraic-decay-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/RadialTransition/InitialSeparation.lean (declaration OAI.RadialTransition.initial_separation)

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

lemma initial_separation {τ ε₀ : ℝ} (hτ : 0 < τ) (hε₀ : 0 < ε₀) :
    ∀ᶠ t : ℝ in atTop, ∀ x ∈ phaseWindow (1/4),
      |onParameters (idealAttraction (grandPressure (corePotential t) t) phaseMass) x-
        onParameters threePlane x| ≤ ε₀ ∧
      HasPhaseGroups (idealAttraction (grandPressure (corePotential t) t) phaseMass) x (τ/2) := by
  sorry

end RadialTransition
end

end OAI
end
