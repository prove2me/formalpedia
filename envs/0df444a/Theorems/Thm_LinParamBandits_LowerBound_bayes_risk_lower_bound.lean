-- Prove2me | Theorems.Thm_LinParamBandits_LowerBound_bayes_risk_lower_bound
-- name    : LinParamBandits.LowerBound.bayes_risk_lower_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T01:18:22.587308+00:00
-- url     : https://prove2.me/theorems/9c48694d-d5c1-4147-93a1-278c63a01f9a
-- title:
--   Theorem 2.1 — on the unit sphere with Z ~ N(0, I_r/r), Risk(T, ψ) ≥ 0.006 r√T and some z has Regret(z, T, ψ) ≥ 0.006 r√T
-- statement:
--   Consider the linear bandit of Section 2: the set of arms is the unit sphere in $\mathbb R^r$ with $r \ge 2$, playing arm $u$ yields $u'Z$ plus standard normal noise, independent across periods and of $Z$, and $Z$ has the multivariate normal distribution with mean $0$ and covariance matrix $I_r/r$.
--
--   **Theorem 2.1 (Lower Bounds).** For all policies $\psi$ and every $T \ge r^2$,
--   $$\mathrm{Risk}(T, \psi) \;\ge\; 0.006\, r \sqrt T.$$
--   Consequently, for any policy $\psi$ and $T \ge r^2$, there exists $z \in \mathbb R^r$ such that
--   $$\mathrm{Regret}(z, T, \psi) \;\ge\; 0.006\, r \sqrt T.$$
--
--   The theorem shows that no policy can have regret or Bayes risk of order smaller than $r\sqrt T$ on the sphere; the phased exploration policy of Section 3 attains this order, so it is optimal up to a constant.
--
--   **Formalization Note** The constant $0.006$ is absolute: it does not depend on $r$, $T$ or $\psi$. The parameter $z$ in the second claim may depend on the policy and is not restricted in norm, as printed. Policies are deterministic and history-dependent, as on p. 3, with each selection rule measurable (implicit in the paper). Regret and risk take values in $[0, \infty]$ as lower Lebesgue integrals of nonnegative gaps. The noise is one i.i.d. standard normal sequence, which gives the same law of the history as the paper's family $W^u_t$ (see the model definition). The footnote on p. 8 (covariance $I_r$) is not part of the theorem and is not stated.
-- source:
--   Rusmevichientong, Tsitsiklis, Linearly Parameterized Bandits, arXiv:0812.3465v2, Theorem 2.1, p. 8 (proof p. 13)

import Mathlib
import Definitions.Def_LinParamBandits_LowerBound_Model

open MeasureTheory ProbabilityTheory

namespace LinParamBandits.LowerBound

/-- Theorem 2.1 (Lower Bounds), Rusmevichientong, Tsitsiklis, arXiv:0812.3465v2, p. 8: arms on the
unit sphere of `ℝ^r`, standard normal noise, `Z ~ N(0, I_r/r)`. For every policy `ψ` and every
`T ≥ r²`, `Risk(T, ψ) ≥ 0.006 r √T`; consequently there is `z ∈ ℝ^r` with
`Regret(z, T, ψ) ≥ 0.006 r √T`. -/
theorem bayes_risk_lower_bound (r : ℕ) (hr : 2 ≤ r) (ψ : SpherePolicy r) (T : ℕ) (hT : r ^ 2 ≤ T) :
    ENNReal.ofReal (0.006 * r * Real.sqrt T) ≤ risk ψ T ∧
      ∃ z : Vec r, ENNReal.ofReal (0.006 * r * Real.sqrt T) ≤ regret ψ z T := by sorry

end LinParamBandits.LowerBound
