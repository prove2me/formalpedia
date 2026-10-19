-- Prove2me | Theorems.Thm_OAI_RadialTransition_family_aligned_box_comparison
-- name    : OAI.RadialTransition.family_aligned_box_comparison
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T01:05:01.662179+00:00
-- url     : https://prove2.me/theorems/b539160b-deca-43b2-8f30-319328e43285
-- title:
--   Finite-volume grand pressures of a family potential in aligned boxes of sides mq/4 and q/4 differ by O(R₀/q) (OpenAI, radial phase transition)
-- statement:
--   Let $m, q \ge 1$ be natural numbers, and let $t \ge 1$, $\beta > 0$, $h$ and $R_0 \ge 2$ be reals. Let $a, R : \mathbb{N} \to \mathbb{R}$ satisfy:
--   - $a_n \ge 0$, $1 \le R_n \le R_0$, and $a$ is summable;
--   - the row condition $2197\, t\, I^{-1} \sum_n a_n \le t^2/64$ (`hrow`), with $I$ = `bumpIntegral`.
--
--   Write $\varphi$ = `familyPotential t a R`. Let $P_L$ = `finiteGrandPressure φ t L β h` be the finite-volume grand pressure in the cube of side $L$, that is $\log(\text{grand partition function})/(tL^3)$. Then
--   $$\bigl|P_{mq/4} - P_{q/4}\bigr| \;\le\; \frac{K\, R_0}{q/4}, \qquad K = \texttt{boxPressureConstant}\ t\ \beta\ h\ \textstyle\sum_n a_n .$$
--
--   The named functions come from the definitions bundle `OAIQWRTD000` of this split. The carver publishes this lemma as an intermediate statement so that each proof fits the platform's verifier.
--
--   Lean: `OAI.RadialTransition.family_aligned_box_comparison`, OpenAI's lemma of that name in `lean/OAI/Probability/RadialTransition/RangeBounds.lean`.
-- source:
--   OpenAI, A radial continuum phase transition with algebraic decay, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 228; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-radial-continuum-phase-transition-with-algebraic-decay-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/RadialTransition/RangeBounds.lean (declaration OAI.RadialTransition.family_aligned_box_comparison)

import Mathlib
import Definitions.Def_OAIQWRTD000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

universe uG uI

noncomputable section

open Function MeasureTheory Set Filter

open scoped ContDiff NNReal BigOperators ENNReal

namespace RadialTransition

lemma family_aligned_box_comparison {m q : ℕ} (hm : 0 < m) (hq : 0 < q)
    {t β h R₀ : ℝ} {a R : ℕ → ℝ} (ht : 1 ≤ t) (hβ : 0 < β)
    (ha : ∀ n, 0 ≤ a n) (hR : ∀ n, 1 ≤ R n) (hs : Summable a)
    (hR₀ : 2 ≤ R₀) (hrange : ∀ n, R n ≤ R₀)
    (hrow : 2197*t*bumpIntegral⁻¹*(∑' n, a n) ≤ (t^2/8)/8) :
    |finiteGrandPressure (familyPotential t a R) t ((m:ℝ)*q/4) β h-
      finiteGrandPressure (familyPotential t a R) t ((q:ℝ)/4) β h| ≤
      boxPressureConstant t β h (∑' n, a n)*R₀/((q:ℝ)/4) := by
  sorry

end RadialTransition

end

end OAI
end
