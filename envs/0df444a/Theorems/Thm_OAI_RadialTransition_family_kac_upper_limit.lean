-- Prove2me | Theorems.Thm_OAI_RadialTransition_family_kac_upper_limit
-- name    : OAI.RadialTransition.family_kac_upper_limit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T01:05:46.114439+00:00
-- url     : https://prove2.me/theorems/008d5cba-1eb6-48e8-be89-553b4ff48402
-- title:
--   Upper bound for the grand pressure of a prepended family by the Kac series (OpenAI, radial phase transition)
-- statement:
--   Let $q \ge 1$, and let $t \ge 1$, $\beta > 0$, $a \ge 0$, $h$ and $R_0 \ge 2$ be reals, with $R \ge q/4 \ge 1$. Let $b, S : \mathbb{N} \to \mathbb{R}$ satisfy:
--   - $b_n \ge 0$, $1 \le S_n \le R_0$, and $b$ is summable;
--   - the row condition $2197\, t\, I^{-1}\bigl(a + \sum_n b_n\bigr) \le t^2/64$ (`hrow`).
--
--   Let $k_n$ = `kacSeries (familyPotential t b S) q R t a β h n` be the Kac series, and assume it is summable. Its $n$-th term is the $n$-particle canonical partition function of the family $(b,S)$ in the box of side $q/4$, weighted by $e^{thn}$ and by a Gaussian-type factor $e^{c n^2/(q/4)^3}$ with $c = \beta t a (1 + \texttt{kernelUpperError}\ q\ R)/2$. Let $P$ be any real with $\log\bigl(\sum_n k_n\bigr)/\bigl(t(q/4)^3\bigr) \le P$. Then the grand pressure of the prepended family potential `familyPotential t (prepend a b) (prepend R S)` at $(\beta, h)$ is at most $P + K R_0/(q/4)$, with $K$ = `boxPressureConstant t β h (∑' n, b n)`.
--
--   The named functions come from the definitions bundle `OAIQWRTD000` of this split. The carver publishes this lemma as an intermediate statement so that each proof fits the platform's verifier.
--
--   Lean: `OAI.RadialTransition.family_kac_upper_limit`, OpenAI's lemma of that name in `lean/OAI/Probability/RadialTransition/KacComparison.lean`.
-- source:
--   OpenAI, A radial continuum phase transition with algebraic decay, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 228; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-radial-continuum-phase-transition-with-algebraic-decay-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/RadialTransition/KacComparison.lean (declaration OAI.RadialTransition.family_kac_upper_limit)

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

lemma family_kac_upper_limit {q : ℕ} (hq : 0 < q) {t β h R₀ a R P : ℝ} {b S : ℕ → ℝ}
    (ht : 1 ≤ t) (hβ : 0 < β) (ha : 0 ≤ a) (hR : (q:ℝ)/4 ≤ R) (hq1 : 1 ≤ (q:ℝ)/4)
    (hb : ∀ n, 0 ≤ b n) (hS : ∀ n, 1 ≤ S n) (hs : Summable b)
    (hR₀ : 2 ≤ R₀) (hrange : ∀ n, S n ≤ R₀)
    (hrow : 2197*t*bumpIntegral⁻¹*(a+∑' n, b n) ≤ (t^2/8)/8)
    (hks : Summable (kacSeries (familyPotential t b S) q R t a β h))
    (hP : Real.log (∑' n, kacSeries (familyPotential t b S) q R t a β h n)/(t*((q:ℝ)/4)^3) ≤ P) :
    grandPressure (familyPotential t (prepend a b) (prepend R S)) t β h ≤
      P+boxPressureConstant t β h (∑' n, b n)*R₀/((q:ℝ)/4) := by
  sorry

end RadialTransition
end

end OAI
end
