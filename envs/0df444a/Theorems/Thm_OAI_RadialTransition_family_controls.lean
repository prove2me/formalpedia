-- Prove2me | Theorems.Thm_OAI_RadialTransition_family_controls
-- name    : OAI.RadialTransition.family_controls
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T01:04:53.143849+00:00
-- url     : https://prove2.me/theorems/607f6aea-d58d-49d3-b9c2-307bf35bc2b2
-- title:
--   Uniform controls for the ideal attraction transform of admissible family pressures (OpenAI, radial phase transition)
-- statement:
--   Let $t \ge 1$ and $A \ge 0$ with $6912A \le t$ and the row condition $2197\, t\, I^{-1} A \le t^2/64$ (`hrow`). Then there are constants $U \ge 1$, $C \ge 1$ and $C_0 > 0$ with the following property. Take any admissible family $(b, S)$ of total mass at most $A$ (`AdmissibleFamily t A b S`) and any $a \in (0, A]$. Write $Q$ = `grandPressure (familyPotential t b S) t` and $Q^{\mathrm{id}}_a$ = `idealAttraction Q a`. Then:
--   1. for all $\beta > 0$ and $h$, the supremum defining $Q^{\mathrm{id}}_a(\beta,h)$ is attained at some shift $u$ (`ActiveShift Q a β h u`);
--   2. for parameters $x = (\beta, h)$ in the window `phaseWindow (1/2)`, a maximizing shift can be chosen in $[0, U]$;
--   3. on `phaseWindow (1/4)`, $Q^{\mathrm{id}}_a$ is $C$-Lipschitz as a function of $x$;
--   4. on `phaseWindow (1/4)`, $0 \le Q^{\mathrm{id}}_a(x) - Q(x) \le C_0\, a$.
--
--   `phaseWindow r` is the closed ball of radius $r$ about the point $(\beta, h) = (1, -3/4)$. It and the other named functions come from the definitions bundle `OAIQWRTD000` of this split. The carver publishes this lemma as an intermediate statement so that each proof fits the platform's verifier.
--
--   Lean: `OAI.RadialTransition.family_controls`, OpenAI's lemma of that name in `lean/OAI/Probability/RadialTransition/FamilyControls.lean`.
-- source:
--   OpenAI, A radial continuum phase transition with algebraic decay, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 228; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-radial-continuum-phase-transition-with-algebraic-decay-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/RadialTransition/FamilyControls.lean (declaration OAI.RadialTransition.family_controls)

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

lemma family_controls {t A : ℝ} (ht : 1 ≤ t) (hA : 0 ≤ A) (htA : 6912*A ≤ t)
    (hrow : 2197*t*bumpIntegral⁻¹*A ≤ (t^2/8)/8) :
    ∃ U C C₀ : ℝ, 1 ≤ U ∧ 1 ≤ C ∧ 0 < C₀ ∧
      ∀ b S : ℕ → ℝ, AdmissibleFamily t A b S → ∀ a ∈ Ioc (0:ℝ) A,
      (∀ β h, 0 < β → ∃ u, ActiveShift (grandPressure (familyPotential t b S) t) a β h u) ∧
      (∀ x ∈ phaseWindow (1/2), ∃ u ∈ Icc (0:ℝ) U,
        ActiveShift (grandPressure (familyPotential t b S) t) a (x 0) (x 1) u) ∧
      (∀ x ∈ phaseWindow (1/4), ∀ y ∈ phaseWindow (1/4),
        |onParameters (idealAttraction (grandPressure (familyPotential t b S) t) a) x-
          onParameters (idealAttraction (grandPressure (familyPotential t b S) t) a) y| ≤ C*dist x y) ∧
      (∀ x ∈ phaseWindow (1/4),
        0 ≤ onParameters (idealAttraction (grandPressure (familyPotential t b S) t) a) x-
          onParameters (grandPressure (familyPotential t b S) t) x ∧
        onParameters (idealAttraction (grandPressure (familyPotential t b S) t) a) x-
          onParameters (grandPressure (familyPotential t b S) t) x ≤ C₀*a) := by
  sorry

end RadialTransition
end

end OAI
end
