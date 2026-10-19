-- Prove2me | Theorems.Thm_OAI_RadialTransition_family_kac_variational_grid
-- name    : OAI.RadialTransition.family_kac_variational_grid
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-19T01:06:00.661262+00:00
-- url     : https://prove2.me/theorems/96cdce35-26eb-48ec-ba8e-2441bd7593c8
-- title:
--   The grand pressure of a prepended family is close to the ideal attraction transform of the old pressure (OpenAI, radial phase transition)
-- statement:
--   Let $q \ge 1$. Take reals $t \ge 1$, $\beta > 0$, $a \ge 0$, $h$ and $R_0 \ge 2$, with $R \ge q/4 \ge 1$. Let $b, S : \mathbb{N} \to \mathbb{R}$ satisfy $b_n \ge 0$, $1 \le S_n \le R_0$, $b$ summable, and the row condition `hrow`. Write $L = q/4$. Assume further, for reals $\kappa, D, F, C$:
--   1. $0 < \kappa \le \beta t^2/3456 - \beta t a (1 + \texttt{kernelUpperError}\ q\ R)/2$;
--   2. $1 \le D$ and $th + \beta t^2/2 + t + 1 \le \kappa D$;
--   3. $D \le F$ and $\exp\bigl(\beta t^2/2 + t(h + \beta a D) + 1\bigr) \le F$;
--   4. `boxPressureConstant t β (h+β*a*v) (∑' n, b n)` $\le C$ for every $v \in [0, D]$.
--
--   Let $Q$ = `grandPressure (familyPotential t b S) t` be the grand pressure of the old family. Let $Q^{\mathrm{id}}_a$ = `idealAttraction Q a` be its ideal attraction transform, $Q^{\mathrm{id}}_a(\beta, h) = \sup_u \bigl(Q(\beta, h + \beta a u) - \tfrac{\beta a}{2}u^2\bigr)$. Let $P^+$ be the grand pressure of the prepended family `familyPotential t (prepend a b) (prepend R S)`. Then
--   $$\bigl|P^+(\beta,h) - Q^{\mathrm{id}}_a(\beta,h)\bigr| \;\le\; \frac{2 C R_0}{L} + \tfrac{\beta a}{2}\,\texttt{kernelRowError}\ q\ R\; F^2 + \frac{\log\bigl((F+2)L^3\bigr)}{t L^3}.$$
--
--   The named functions come from the definitions bundle `OAIQWRTD000` of this split. The carver publishes this lemma as an intermediate statement so that each proof fits the platform's verifier.
--
--   Lean: `OAI.RadialTransition.family_kac_variational_grid`, OpenAI's lemma of that name in `lean/OAI/Probability/RadialTransition/KacVariational.lean`.
-- source:
--   OpenAI, A radial continuum phase transition with algebraic decay, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 228; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/A-radial-continuum-phase-transition-with-algebraic-decay-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/RadialTransition/KacVariational.lean (declaration OAI.RadialTransition.family_kac_variational_grid)

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

lemma family_kac_variational_grid {q : ℕ} (hq : 0 < q)
    {t β h R₀ a R κ D F C : ℝ} {b S : ℕ → ℝ}
    (ht : 1 ≤ t) (hβ : 0 < β) (ha : 0 ≤ a) (hR : (q:ℝ)/4 ≤ R) (hq1 : 1 ≤ (q:ℝ)/4)
    (hb : ∀ n, 0 ≤ b n) (hS : ∀ n, 1 ≤ S n) (hs : Summable b)
    (hR₀ : 2 ≤ R₀) (hrange : ∀ n, S n ≤ R₀)
    (hrow : 2197*t*bumpIntegral⁻¹*(a+∑' n, b n) ≤ (t^2/8)/8)
    (hκ : 0 < κ) (hc : κ ≤ β*(t^2/3456)-β*t*a*(1+kernelUpperError q R)/2)
    (hD : 1 ≤ D) (hcut : t*h+β*(t^2/2)+t+1 ≤ κ*D)
    (hDF : D ≤ F) (hF : Real.exp (β*(t^2/2)+t*(h+β*a*D)+1) ≤ F)
    (hC : ∀ v ∈ Icc (0:ℝ) D, boxPressureConstant t β (h+β*a*v) (∑' n, b n) ≤ C) :
    |grandPressure (familyPotential t (prepend a b) (prepend R S)) t β h-
      idealAttraction (grandPressure (familyPotential t b S) t) a β h| ≤
      2*C*R₀/((q:ℝ)/4)+β*a/2*kernelRowError q R*F^2+
        Real.log ((F+2)*((q:ℝ)/4)^3)/(t*((q:ℝ)/4)^3) := by
  sorry

end RadialTransition
end

end OAI
end
