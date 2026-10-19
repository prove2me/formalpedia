-- Prove2me | Theorems.Thm_OAI_RadialTransition_grandPressure_reversePrefix_tendsto
-- name    : OAI.RadialTransition.grandPressure_reversePrefix_tendsto
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T01:06:25.980146+00:00
-- url     : https://prove2.me/theorems/03bd37ae-1cb0-4a11-975f-4afaea1e1a78
-- title:
--   Grand pressures of the truncated attraction families converge to that of the full family (OpenAI, radial phase transition)
-- statement:
--   Let $t \ge 1$, $\beta > 0$ and $h$ be reals. Let $a, R : \mathbb{N} \to \mathbb{R}$ be an admissible family with total mass at most $A$ (`AdmissibleFamily t A a R`): $a_n \ge 0$, $R_n \ge 1$, $a$ summable, and $\sum_n a_n \le A$. Assume the row condition $2197\, t\, A / I \le t^2/64$ (`hrow`), where $I$ = `bumpIntegral` is the integral of the bump.
--
--   The family potential $\varphi_{t,a,R}$ = `familyPotential t a R` is the core potential `coreReal t` minus $t\sum_n a_n$ times the bump profile at scale $R_n$. For the truncations, use the first $n$ terms in reverse order, padded with $a = 0$ and $R = 1$ (`reversePrefix 0 a n`, `reversePrefix 1 R n`). Then the grand pressures of the truncated potentials converge, as $n \to \infty$, to the grand pressure `grandPressure (familyPotential t a R) t β h` of the full family.
--
--   `AdmissibleFamily`, `familyPotential`, `reversePrefix`, `bumpIntegral` and `grandPressure` come from the definitions bundle `OAIQWRTD000` of this split. The carver publishes this lemma as an intermediate statement so that each proof fits the platform's verifier.
--
--   Lean: `OAI.RadialTransition.grandPressure_reversePrefix_tendsto`, OpenAI's lemma of that name in `lean/OAI/Probability/RadialTransition/TruncatedFamily.lean`.
-- source:
--   OpenAI, A radial continuum phase transition with algebraic decay, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 228; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-radial-continuum-phase-transition-with-algebraic-decay-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/RadialTransition/TruncatedFamily.lean (declaration OAI.RadialTransition.grandPressure_reversePrefix_tendsto)

import Mathlib
import Definitions.Def_OAIQWRTD000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open scoped BigOperators NNReal
open Set Filter
namespace RadialTransition

lemma grandPressure_reversePrefix_tendsto {t A β h : ℝ} {a R : ℕ → ℝ}
    (ht : 1 ≤ t) (hβ : 0 < β) (had : AdmissibleFamily t A a R)
    (hrow : 2197*t*bumpIntegral⁻¹*A ≤ (t^2/8)/8) :
    Tendsto (fun n => grandPressure (familyPotential t (reversePrefix 0 a n) (reversePrefix 1 R n)) t β h)
      atTop (nhds (grandPressure (familyPotential t a R) t β h)) := by
  sorry

end RadialTransition
end

end OAI
end
