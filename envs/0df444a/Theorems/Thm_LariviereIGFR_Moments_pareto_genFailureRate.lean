-- Prove2me | Theorems.Thm_LariviereIGFR_Moments_pareto_genFailureRate
-- name    : LariviereIGFR.Moments.pareto_genFailureRate
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:31:54.869221+00:00
-- url     : https://prove2.me/theorems/f9057672-4796-43f8-93b8-de17b3f13548
-- title:
--   §3 preamble, p. 603 — the Pareto law has g(ξ) = k for ξ ≥ S
-- statement:
--   Let $S>0$ and $k>0$, and let $X_k$ be a Pareto random variable with scale $S$ and parameter $k$, i.e. with density
--   $$
--   \phi(\xi)=kS^k\xi^{-k-1}\quad(\xi\ge S),\qquad \phi(\xi)=0\quad(\xi<S).
--   $$
--   Its generalized failure rate $g(\xi)=\xi\phi(\xi)/\bar\Phi(\xi)$ is constant:
--   $$
--   g(\xi)=k\qquad\text{for all }\xi\ge S.
--   $$
--
--   The Pareto plays for IGFR laws the role the exponential plays for IFR laws: it is the law with constant generalized failure rate, and the paper's moment theorem is proved by comparison with it.
--
--   **Formalization Note** The law is Mathlib's `paretoMeasure S k` with density `paretoPDFReal S k` (scale `S`, rate `k`), whose value at $\xi=S$ is $k/S$, as in the printed formula.
-- source:
--   Lariviere, A note on probability distributions with increasing generalized failure rates, Oper. Res. 54(3) (2006), p. 603, §3 preamble

import Mathlib
import Definitions.Def_LariviereIGFR_Moments_Setting

namespace LariviereIGFR.Moments

open MeasureTheory ProbabilityTheory

/-- §3 preamble, p. 603: the Pareto law with density `k S^k ξ^(-k-1)` on `ξ ≥ S > 0` has constant
generalized failure rate `g(ξ) = k` for `ξ ≥ S`. -/
theorem pareto_genFailureRate (S k : ℝ) (hS : 0 < S) (hk : 0 < k) :
    ∀ ξ, S ≤ ξ → LariviereIGFR.Char.genFailureRate (paretoMeasure S k) (paretoPDFReal S k) ξ = k := by sorry

end LariviereIGFR.Moments
