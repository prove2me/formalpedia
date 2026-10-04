-- Prove2me | Theorems.Thm_MeanFieldOpt_ControlDuality_value_at_origin
-- name    : MeanFieldOpt.ControlDuality.value_at_origin
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T04:28:39.285081+00:00
-- url     : https://prove2.me/theorems/2fb5e313-d5a0-4e68-acb9-f92852827067
-- title:
--   Section 7.1, p. 34 — $V(0,0)=\mathsf P(\gamma)$
-- statement:
--   Let $\xi$ be a mixture, $\gamma\in\mathsf{SF}_+$, $\nu(t)=\int_t^1\xi''(s)\gamma(s)\,ds$, and $V$ the function of Eq. (7.2). Then
--   $$V(0,0)=\inf_x\Phi_\gamma(0,x)-\frac12\int_0^1\nu(s)\,ds=\Phi_\gamma(0,0)-\frac12\int_0^1 s\,\xi''(s)\gamma(s)\,ds=\mathsf P(\gamma).$$
--
--   Combined with Proposition 7.1 at $(t,z)=(0,0)$, this gives Proposition 4.1.
-- source:
--   El Alaoui, Montanari, Sellke, Optimization of Mean-field Spin Glasses, arXiv:2001.00904v1, p. 34, Section 7.1, display after Proposition 7.1

import Mathlib
import Definitions.Def_MeanFieldOpt_ControlDuality_Parisi

namespace MeanFieldOpt.ControlDuality

/-- Section 7.1, p. 34 (arXiv:2001.00904v1), the evaluation after Proposition 7.1: for
`γ ∈ SF₊`, `V(0, 0) = inf_x Φ_γ(0, x) − ½ ∫_0^1 ν(s) ds = Φ_γ(0, 0) − ½ ∫_0^1 s ξ''(s) γ(s) ds
= P(γ)`. -/
theorem value_at_origin (ξ : Mixture) (d : SFData) : V ξ d 0 0 = Parisi ξ d := by sorry

end MeanFieldOpt.ControlDuality
