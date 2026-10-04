-- Prove2me | Theorems.Thm_MeanFieldOpt_ControlDuality_proposition_7_1
-- name    : MeanFieldOpt.ControlDuality.proposition_7_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T04:45:47.935666+00:00
-- url     : https://prove2.me/theorems/172bfdf9-bce0-4add-8321-3880e09b8e53
-- title:
--   Proposition 7.1 — $\mathcal J_\gamma(t,z)=V(t,z)$ on $[0,1]\times(-1,1)$
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space carrying a standard Brownian motion $B$, let $\xi$ be a mixture and $\gamma\in\mathsf{SF}_+$. For all $(t,z)\in[0,1]\times(-1,1)$,
--   $$\mathcal J_\gamma(t,z)=V(t,z),$$
--   where $\mathcal J_\gamma(t,z)$ is the value (4.5) of the stochastic control problem — the supremum, over controls $u\in D[t,1]$ with $z+\int_t^1\sqrt{\xi''(s)}u_s\,dB_s\in(-1,1)$ a.s., of
--   $$\mathbb E\Big[\int_t^1\xi''(s)u_s\,ds+\frac12\int_t^1\nu(s)\big(\xi''(s)u_s^2-1\big)ds\Big]$$
--   — and $V(t,z)=\Phi^*_\gamma(t,z)-\frac12\nu(t)z^2-\frac12\int_t^1\nu(s)\,ds$ (Eq. (7.2)).
--
--   This is the verification theorem: the explicit function built from the Parisi PDE is the value function of the control problem.
--
--   **Formalization Note** "$\mathcal J_\gamma(t,z)=V(t,z)$" is stated as: $V(t,z)$ is the least upper bound of the set of objective values of admissible controls. This asserts both that the set is bounded above and that its supremum is $V(t,z)$, and no default value of a real supremum can occur. Each $B_r$ is assumed measurable.
-- source:
--   El Alaoui, Montanari, Sellke, Optimization of Mean-field Spin Glasses, arXiv:2001.00904v1, p. 34, Proposition 7.1

import Mathlib
import Definitions.Def_MeanFieldOpt_ControlDuality_Control

open MeasureTheory ProbabilityTheory Set
open scoped NNReal

namespace MeanFieldOpt.ControlDuality

/-- Proposition 7.1 (arXiv:2001.00904v1, p. 34): for `γ ∈ SF₊` and all
`(t, z) ∈ [0, 1] × (−1, 1)`, `𝒥_γ(t, z) = V(t, z)`, where `𝒥_γ` is the value (4.5) of the
stochastic control problem driven by a standard Brownian motion `B` and `V` is Eq. (7.2). The
equality of the supremum is stated as: `V(t, z)` is the least upper bound of the objective values
of admissible controls. -/
theorem proposition_7_1 (ξ : Mixture) (d : SFData) {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (B : ℝ≥0 → Ω → ℝ)
    (hBm : ∀ r, Measurable (B r)) (hB : IsBrownianReal B P) :
    ∀ t ∈ Icc (0 : ℝ) 1, ∀ z ∈ Ioo (-1 : ℝ) 1,
      IsLUB (controlValues ξ d P B hBm t z) (V ξ d t z) := by sorry

end MeanFieldOpt.ControlDuality
