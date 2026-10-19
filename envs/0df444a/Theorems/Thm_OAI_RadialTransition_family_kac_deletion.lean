-- Prove2me | Theorems.Thm_OAI_RadialTransition_family_kac_deletion
-- name    : OAI.RadialTransition.family_kac_deletion
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T01:05:52.37798+00:00
-- url     : https://prove2.me/theorems/05eeb23a-2c7b-4ac2-b5eb-89d3c01d9a21
-- title:
--   Deleting the new attraction term: finite pressure of the prepended family vs. the deleted Kac pressure (OpenAI, radial phase transition)
-- statement:
--   Let $m, q \ge 1$ be natural numbers, and let $t \ge 1$, $\beta > 0$, $a \ge 0$, $R \ge 1$, $h$ and $R_0 \ge 2$ be reals. Let $b, S : \mathbb{N} \to \mathbb{R}$ satisfy:
--   - $b_n \ge 0$, $1 \le S_n \le R_0$, and $b$ is summable;
--   - the row condition $2197\, t\, I^{-1}\bigl(a + \sum_n b_n\bigr) \le t^2/64$ (`hrow`), with $I$ = `bumpIntegral`.
--
--   Prepend the term $(a, R)$ to the family $(b, S)$ (`prepend a b`, `prepend R S`). Compare two quantities in the box of side $mq/4$:
--   - the finite-volume grand pressure `finiteGrandPressure` of the prepended family potential;
--   - the "deleted Kac pressure" `deletedKacPressure (familyPotential t b S) m q R t a β h`. This is a log partition function on the grid of $m^3$ macro-cells of side $q/4$. In it, the potential of $(b,S)$ acts only within each cell, and the new term $(a,R)$ acts through a Kac-type pair energy between cells (`macroKacEnergy`).
--
--   They differ by at most $K R_0/(q/4)$, with $K$ = `boxPressureConstant t β h (∑' n, b n)`.
--
--   The named functions come from the definitions bundle `OAIQWRTD000` of this split. The carver publishes this lemma as an intermediate statement so that each proof fits the platform's verifier.
--
--   Lean: `OAI.RadialTransition.family_kac_deletion`, OpenAI's lemma of that name in `lean/OAI/Probability/RadialTransition/KacDeletion.lean`.
-- source:
--   OpenAI, A radial continuum phase transition with algebraic decay, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 228; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-radial-continuum-phase-transition-with-algebraic-decay-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/RadialTransition/KacDeletion.lean (declaration OAI.RadialTransition.family_kac_deletion)

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

lemma family_kac_deletion {m q : ℕ} (hm : 0 < m) (hq : 0 < q)
    {t β h R₀ a R : ℝ} {b S : ℕ → ℝ} (ht : 1 ≤ t) (hβ : 0 < β) (ha : 0 ≤ a) (hR : 1 ≤ R)
    (hb : ∀ n, 0 ≤ b n) (hS : ∀ n, 1 ≤ S n) (hs : Summable b)
    (hR₀ : 2 ≤ R₀) (hrange : ∀ n, S n ≤ R₀)
    (hrow : 2197*t*bumpIntegral⁻¹*(a+∑' n, b n) ≤ (t^2/8)/8) :
    |finiteGrandPressure (familyPotential t (prepend a b) (prepend R S)) t ((m:ℝ)*q/4) β h-
      deletedKacPressure (familyPotential t b S) m q R t a β h| ≤
      boxPressureConstant t β h (∑' n, b n)*R₀/((q:ℝ)/4) := by
  sorry

end RadialTransition
end

end OAI
end
