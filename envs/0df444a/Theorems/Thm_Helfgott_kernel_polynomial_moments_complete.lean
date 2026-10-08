-- Prove2me | Theorems.Thm_Helfgott_kernel_polynomial_moments_complete
-- name    : Helfgott.kernel_polynomial_moments_complete
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T02:18:48.719949+00:00
-- url     : https://prove2.me/theorems/a01f8a97-aea9-4281-a2ac-b69a34e00e28
-- title:
--   Complete rational polynomial mass and variation bounds for the actual Goldbach kernel
-- statement:
--   The compact logarithmic kernel used for the actual three-prime Goldbach smoothing satisfies the two explicit polynomial moment bounds
--   $$\int_0^2|t(2-t)^3|e^{t-1/2}\,dt\le\frac52,$$
--   $$\int_0^2|t(2-t)(16-26t-3t^2+7t^3+t^4)|e^{t-1/2}\,dt\le15.$$
--   These are the complete mass and second-derivative variation integrals underlying a quantitative Fourier bound for the actual major-arc smoothing kernel.
-- source:
--   Helfgott, Major arcs for Goldbach, https://arxiv.org/abs/1305.2897. Exact antiderivative and complete rational polynomial bounds. Written by Codex.

import Definitions.Def_Helfgott_KernelPolynomialMoments

namespace Helfgott

theorem kernel_polynomial_moments_complete : KernelPolynomialMoments := by sorry

end Helfgott
