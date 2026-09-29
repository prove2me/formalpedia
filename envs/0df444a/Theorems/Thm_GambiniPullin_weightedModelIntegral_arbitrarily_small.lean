-- Prove2me | Theorems.Thm_GambiniPullin_weightedModelIntegral_arbitrarily_small
-- name    : GambiniPullin.weightedModelIntegral_arbitrarily_small
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T15:17:59.795493+00:00
-- url     : https://prove2.me/theorems/79f7661b-1fbb-45d3-bca7-2c0f1869ff04
-- title:
--   Gambini–Pullin, Appendix A: the weighted model integral can be made arbitrarily small
-- statement:
--   For every lattice parameter $\sigma > 0$ and every $\varepsilon > 0$ there exist weights $\alpha > 0$ and $\beta > 0$ such that the weighted model integral (A.2) satisfies $$\left|\int_{\mathbb R^2} e^{-\alpha x^2}e^{-\beta(x^2+y^2)}\frac{x^2-y^2}{\bigl(1+x^2+\frac{y^2}{1+\sigma y^2}\bigr)^2}\,dx\,dy\right| < \varepsilon.$$
-- source:
--   R. Gambini and J. Pullin, Emergence of stringlike physics from Lorentz invariance in loop quantum gravity, Int. J. Mod. Phys. D 23 (2014) 1442023, https://doi.org/10.1142/S0218271814420231, p. 1442023-5, Appendix A, sentence after eq. (A.2): '... one can see that with suitable choices of α and β one can make the integral as small as desired.'

import Mathlib
import Definitions.Def_GambiniPullin_AppendixA_Defs

open MeasureTheory Filter

namespace GambiniPullin

theorem weightedModelIntegral_arbitrarily_small (σ : ℝ) (hσ : 0 < σ) (ε : ℝ)
    (hε : 0 < ε) :
    ∃ α : ℝ, 0 < α ∧ ∃ β : ℝ, 0 < β ∧ |weightedModelIntegral α β σ| < ε := by sorry

end GambiniPullin
