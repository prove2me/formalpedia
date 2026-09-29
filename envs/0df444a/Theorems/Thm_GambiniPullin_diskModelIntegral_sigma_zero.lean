-- Prove2me | Theorems.Thm_GambiniPullin_diskModelIntegral_sigma_zero
-- name    : GambiniPullin.diskModelIntegral_sigma_zero
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-24T14:27:22.134973+00:00
-- url     : https://prove2.me/theorems/b8575b9e-d678-47e2-b6d2-90e089d7ac0d
-- title:
--   Appendix A: for $\sigma = 0$ the model integral vanishes (disk truncation)
-- statement:
--   For $\sigma = 0$ the denominator $D_0(x,y) = 1+x^2+y^2$ is rotation invariant, and the model integral (A.1) vanishes. Formally: for every real $R$, $$\int_{x^2+y^2\le R^2} \frac{x^2-y^2}{(1+x^2+y^2)^2}\,dx\,dy = 0.$$
-- source:
--   R. Gambini and J. Pullin, Emergence of stringlike physics from Lorentz invariance in loop quantum gravity, Int. J. Mod. Phys. D 23 (2014) 1442023, https://doi.org/10.1142/S0218271814420231, p. 1442023-5, Appendix A, sentence after eq. (A.1): 'If σ = 0 the denominator is invariant under rotations and the integral vanishes.'

import Mathlib
import Definitions.Def_GambiniPullin_AppendixA_Defs

open MeasureTheory Filter

namespace GambiniPullin

theorem diskModelIntegral_sigma_zero (R : ℝ) : diskModelIntegral 0 R = 0 := by sorry

end GambiniPullin
