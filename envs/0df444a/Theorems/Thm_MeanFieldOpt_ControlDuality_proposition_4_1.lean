-- Prove2me | Theorems.Thm_MeanFieldOpt_ControlDuality_proposition_4_1
-- name    : MeanFieldOpt.ControlDuality.proposition_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T04:46:14.956308+00:00
-- url     : https://prove2.me/theorems/a9194ba7-9c7d-4409-b6da-1f3f4dde3e93
-- title:
--   Proposition 4.1 — for $\gamma\in\mathsf{SF}_+$, $\mathcal J_\gamma(0,0)=\mathsf P(\gamma)$
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space carrying a standard Brownian motion $(B_s)_{s\ge0}$ with natural filtration, let $\xi(t)=\sum_{k\ge2}c_k^2t^k$ be a mixture with $\xi(1+\varepsilon)<\infty$, and let $\gamma\in\mathsf{SF}_+$ be a nonnegative step function on $[0,1)$. Put $\nu(t)=\int_t^1\xi''(s)\gamma(s)\,ds$. Then
--   $$\sup_{u}\ \mathbb E\Big[\int_0^1\xi''(s)u_s\,ds+\frac12\int_0^1\nu(s)\big(\xi''(s)u_s^2-1\big)ds\Big]=\mathsf P(\gamma)=\Phi_\gamma(0,0)-\frac12\int_0^1 t\,\xi''(t)\gamma(t)\,dt,$$
--   where the supremum runs over progressively measurable processes $u$ with $\mathbb E\int_0^1\xi''(s)u_s^2\,ds<\infty$ and $\int_0^1\sqrt{\xi''(s)}\,u_s\,dB_s\in(-1,1)$ almost surely, and $\Phi_\gamma$ is the solution of the Parisi PDE with $\Phi_\gamma(1,x)=|x|$. In the paper's notation, $\mathcal J_\gamma(0,0)=\mathsf P(\gamma)$.
--
--   The left-hand side is the Lagrangian relaxation, with multiplier $\tfrac12\xi''\gamma$, of the stochastic control problem whose value bounds the energy reached by message-passing algorithms; the proposition identifies it with the Parisi functional.
--
--   **Formalization Note** The supremum is stated as a least upper bound (`IsLUB`), which also asserts that the objective values are bounded above. The stochastic integral is the $L^2$ Itô integral of the published definition `Peng1990.SMP.IsItoIntegral`. Each $B_s$ is assumed measurable. No hypothesis on $\xi$ beyond the paper's is needed: for $\xi\equiv0$ both sides are $0$.
-- source:
--   El Alaoui, Montanari, Sellke, Optimization of Mean-field Spin Glasses, arXiv:2001.00904v1, p. 11, Proposition 4.1

import Mathlib
import Definitions.Def_MeanFieldOpt_ControlDuality_Control

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace MeanFieldOpt.ControlDuality

/-- Proposition 4.1 (arXiv:2001.00904v1, p. 11): for `γ ∈ SF₊`, `𝒥_γ(0, 0) = P(γ)`. The value
`𝒥_γ(0, 0)` of the stochastic control problem (4.5), driven by a standard Brownian motion `B`, is
the supremum of the objective values of admissible controls started at `(t, z) = (0, 0)`; the
statement says that the Parisi functional `P(γ)` (Eq. (1.6)) is their least upper bound. -/
theorem proposition_4_1 (ξ : Mixture) (d : SFData) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hBm : ∀ r, Measurable (B r)) (hB : IsBrownianReal B P) :
    IsLUB (controlValues ξ d P B hBm 0 0) (Parisi ξ d) := by sorry

end MeanFieldOpt.ControlDuality
