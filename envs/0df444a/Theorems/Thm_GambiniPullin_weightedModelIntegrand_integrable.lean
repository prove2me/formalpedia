-- Prove2me | Theorems.Thm_GambiniPullin_weightedModelIntegrand_integrable
-- name    : GambiniPullin.weightedModelIntegrand_integrable
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T15:07:02.463846+00:00
-- url     : https://prove2.me/theorems/70e6ad79-0f98-41f5-bfec-81eb9c9ac03b
-- title:
--   Appendix A: the weighted model integrand (A.2) is integrable
-- statement:
--   For $\alpha \ge 0$, $\beta > 0$, $\sigma \ge 0$, the integrand of (A.2), $$e^{-\alpha x^2}e^{-\beta(x^2+y^2)}\,\frac{x^2-y^2}{\bigl(1+x^2+\frac{y^2}{1+\sigma y^2}\bigr)^2},$$ is Lebesgue integrable on $\mathbb R^2$, so the weighted integral (A.2) is a genuine (absolutely convergent) integral.
-- source:
--   R. Gambini and J. Pullin, Emergence of stringlike physics from Lorentz invariance in loop quantum gravity, Int. J. Mod. Phys. D 23 (2014) 1442023, https://doi.org/10.1142/S0218271814420231, p. 1442023-5, Appendix A, eq. (A.2) (well-definedness of the weighted integral, implicit in the source).

import Mathlib
import Definitions.Def_GambiniPullin_AppendixA_Defs

open MeasureTheory Filter

namespace GambiniPullin

theorem weightedModelIntegrand_integrable (α β σ : ℝ) (hα : 0 ≤ α) (hβ : 0 < β)
    (hσ : 0 ≤ σ) :
    Integrable (fun p : ℝ × ℝ => weightedModelIntegrand α β σ p.1 p.2) := by sorry

end GambiniPullin
