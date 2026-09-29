-- Prove2me | Theorems.Thm_GambiniPullin_weightedModelIntegral_diag_tendsto_zero
-- name    : GambiniPullin.weightedModelIntegral_diag_tendsto_zero
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T15:10:14.870405+00:00
-- url     : https://prove2.me/theorems/fb23b1db-c341-4cdb-8edf-569fd051c6ba
-- title:
--   Appendix A: $I(\beta,\beta,\sigma)\to 0$ as $\beta\to\infty$
-- statement:
--   For each $\sigma > 0$, taking the two weights equal ($\alpha = \beta$, the regime '$\alpha \sim \beta$') and letting $\beta \to \infty$, the weighted integral (A.2) tends to $0$: $$\lim_{\beta\to\infty} \int_{\mathbb R^2} e^{-\beta x^2}e^{-\beta(x^2+y^2)}\frac{x^2-y^2}{\bigl(1+x^2+\frac{y^2}{1+\sigma y^2}\bigr)^2}\,dx\,dy = 0.$$
-- source:
--   R. Gambini and J. Pullin, Emergence of stringlike physics from Lorentz invariance in loop quantum gravity, Int. J. Mod. Phys. D 23 (2014) 1442023, https://doi.org/10.1142/S0218271814420231, p. 1442023-5, Appendix A, last sentences: 'This is due to the exponentials cutting off the integral in the region (large values of x, y) that yielded the nonvanishing contributions. More precisely one needs α ∼ β and both larger than σ.'

import Mathlib
import Definitions.Def_GambiniPullin_AppendixA_Defs

open MeasureTheory Filter

namespace GambiniPullin

theorem weightedModelIntegral_diag_tendsto_zero (σ : ℝ) (hσ : 0 < σ) :
    Tendsto (fun β => weightedModelIntegral β β σ) atTop (nhds 0) := by sorry

end GambiniPullin
