-- Prove2me | Theorems.Thm_GambiniPullin_weightedModelIntegral_rotational_zero
-- name    : GambiniPullin.weightedModelIntegral_rotational_zero
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T15:09:12.699418+00:00
-- url     : https://prove2.me/theorems/2f786039-2a0f-45c2-ab66-af08007aab83
-- title:
--   Appendix A: with only the rotation-invariant weight and $\sigma=0$, (A.2) vanishes
-- statement:
--   When the fuzziness weight is switched off ($\alpha = 0$) and $\sigma = 0$, the remaining weight $e^{-\beta(x^2+y^2)}$ is rotation invariant and the weighted integral still vanishes: for every $\beta > 0$, $$\int_{\mathbb R^2} e^{-\beta(x^2+y^2)}\frac{x^2-y^2}{(1+x^2+y^2)^2}\,dx\,dy = 0.$$
-- source:
--   R. Gambini and J. Pullin, Emergence of stringlike physics from Lorentz invariance in loop quantum gravity, Int. J. Mod. Phys. D 23 (2014) 1442023, https://doi.org/10.1142/S0218271814420231, p. 1442023-5, Appendix A, after eq. (A.2): '... the second representing the nonlocal interaction (in this case rotationally invariant, in the case of interest, Lorentz invariant)', combined with the σ = 0 vanishing after (A.1).

import Mathlib
import Definitions.Def_GambiniPullin_AppendixA_Defs

open MeasureTheory Filter

namespace GambiniPullin

theorem weightedModelIntegral_rotational_zero (β : ℝ) (hβ : 0 < β) :
    weightedModelIntegral 0 β 0 = 0 := by sorry

end GambiniPullin
