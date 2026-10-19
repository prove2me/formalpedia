-- Prove2me | Theorems.Thm_OAI_RadialTransition_family_kac_lower_limit
-- name    : OAI.RadialTransition.family_kac_lower_limit
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T01:05:31.088045+00:00
-- url     : https://prove2.me/theorems/574d9086-46c7-49ce-aced-5b0edd7665bc
-- title:
--   Lower bound for the grand pressure of a prepended family by a shifted finite pressure (OpenAI, radial phase transition)
-- statement:
--   Take the hypotheses of `family_kac_upper_limit`:
--   - $q \ge 1$, and reals $t \ge 1$, $\beta > 0$, $a \ge 0$, $h$ and $R_0 \ge 2$, with $R \ge q/4 \ge 1$;
--   - $b, S : \mathbb{N} \to \mathbb{R}$ with $b_n \ge 0$, $1 \le S_n \le R_0$, and $b$ summable;
--   - the row condition `hrow`;
--   - summability of the Kac series `kacSeries (familyPotential t b S) q R t a β h`.
--
--   Let $u$ and $D$ be reals with $\exp\bigl(\beta t^2/2 + t(h + \beta a u) + 1\bigr) \le D$ (`hD`). Write $L = q/4$, $\varphi = $ `familyPotential t b S`, and $\varphi^+ = $ `familyPotential t (prepend a b) (prepend R S)`. Then
--   $$P^{\mathrm{fin}}_{\varphi,L}(\beta, h + \beta a u) - \tfrac{\beta a}{2} u^2 \;\le\; P_{\varphi^+}(\beta, h) + \frac{K R_0}{L} + \tfrac{\beta a}{2}\,\varepsilon_{q,R}\, D^2 + \frac{\log\bigl((D+2)L^3\bigr)}{t L^3}.$$
--   The quantities are:
--   - $P^{\mathrm{fin}}_{\varphi,L}$ = `finiteGrandPressure φ t L`, the finite-volume grand pressure;
--   - $P_{\varphi^+}$ = `grandPressure φ⁺ t`, the grand pressure;
--   - $K$ = `boxPressureConstant t β h (∑' n, b n)`;
--   - $\varepsilon_{q,R}$ = `kernelRowError q R`.
--
--   The named functions come from the definitions bundle `OAIQWRTD000` of this split. The carver publishes this lemma as an intermediate statement so that each proof fits the platform's verifier.
--
--   Lean: `OAI.RadialTransition.family_kac_lower_limit`, OpenAI's lemma of that name in `lean/OAI/Probability/RadialTransition/KacComparison.lean`.
-- source:
--   OpenAI, A radial continuum phase transition with algebraic decay, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 228; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-radial-continuum-phase-transition-with-algebraic-decay-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/RadialTransition/KacComparison.lean (declaration OAI.RadialTransition.family_kac_lower_limit)

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

lemma family_kac_lower_limit {q : ℕ} (hq : 0 < q) {t β h R₀ a R D u : ℝ} {b S : ℕ → ℝ}
    (ht : 1 ≤ t) (hβ : 0 < β) (ha : 0 ≤ a) (hR : (q:ℝ)/4 ≤ R) (hq1 : 1 ≤ (q:ℝ)/4)
    (hb : ∀ n, 0 ≤ b n) (hS : ∀ n, 1 ≤ S n) (hs : Summable b)
    (hR₀ : 2 ≤ R₀) (hrange : ∀ n, S n ≤ R₀)
    (hrow : 2197*t*bumpIntegral⁻¹*(a+∑' n, b n) ≤ (t^2/8)/8)
    (hks : Summable (kacSeries (familyPotential t b S) q R t a β h))
    (hD : Real.exp (β*(t^2/2)+t*(h+β*a*u)+1) ≤ D) :
    finiteGrandPressure (familyPotential t b S) t ((q:ℝ)/4) β (h+β*a*u)-β*a/2*u^2 ≤
      grandPressure (familyPotential t (prepend a b) (prepend R S)) t β h+
      boxPressureConstant t β h (∑' n, b n)*R₀/((q:ℝ)/4)+
      β*a/2*kernelRowError q R*D^2+Real.log ((D+2)*((q:ℝ)/4)^3)/(t*((q:ℝ)/4)^3) := by
  sorry

end RadialTransition
end

end OAI
end
