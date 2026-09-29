-- Prove2me | Theorems.Thm_GambiniPullin_diskModelIntegral_tendsto_atBot
-- name    : GambiniPullin.diskModelIntegral_tendsto_atBot
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T14:32:49.563763+00:00
-- url     : https://prove2.me/theorems/a6861d8d-e5a6-4546-a605-cab7fca4d895
-- title:
--   Appendix A: for $\sigma>0$ the truncated model integral diverges to $-\infty$
-- statement:
--   For $\sigma > 0$ rotational invariance is broken and the model integral (A.1) does not vanish by a significant amount: the disk-truncated integrals $$I^{\mathrm{disk}}_\sigma(R) = \int_{x^2+y^2\le R^2} \frac{x^2-y^2}{\bigl(1+x^2+\frac{y^2}{1+\sigma y^2}\bigr)^2}\,dx\,dy$$ tend to $-\infty$ as $R \to +\infty$.
-- source:
--   R. Gambini and J. Pullin, Emergence of stringlike physics from Lorentz invariance in loop quantum gravity, Int. J. Mod. Phys. D 23 (2014) 1442023, https://doi.org/10.1142/S0218271814420231, p. 1442023-5, Appendix A, after eq. (A.1): 'When it is not zero, the different behavior in x and y for large values implies the integral does not vanish by a significant amount.'

import Mathlib
import Definitions.Def_GambiniPullin_AppendixA_Defs

open MeasureTheory Filter

namespace GambiniPullin

theorem diskModelIntegral_tendsto_atBot (σ : ℝ) (hσ : 0 < σ) :
    Tendsto (fun R => diskModelIntegral σ R) atTop atBot := by sorry

end GambiniPullin
