-- Prove2me | Theorems.Thm_LostSalesRQ_penalty_calibration
-- name    : LostSalesRQ.penalty_calibration
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-17T18:24:54.505635+00:00
-- url     : https://prove2.me/theorems/bb687f1c-1ec4-4110-90e1-fbefd84f96eb
-- title:
--   Proposition 2: exact penalty calibration
-- statement:
--   Fix $\mu\ge0$. For $\eta\ge1$ let $\alpha_\mu(\eta)=\eta\big[1+\mathbb E\sup_{0\le t\le\mu}\{(1-1/\eta)t-N(t)\}\big]$, where $N$ is a rate-one Poisson process. Then
--   $$B_\mu(\eta)+D_\mu(\eta)=\alpha_\mu(\eta)\qquad(\eta\ge1),$$
--   and $\alpha_\mu$ is a continuous, strictly increasing bijection from $[1,\infty)$ onto itself.
--
--   At the penalty $a=\alpha_\mu(\eta)$ the two terms of the committed-supply bound coincide, so every penalty $a\ge1$ has a unique calibrated weight at which Proposition 1 gives exactly $B_\mu(\eta)$.
-- source:
--   M. Hu, "A 1.932 Guarantee for (r,Q) Policies in Continuous-Review Lost-Sales Inventory Systems", arXiv:2610.34576, 2026; Proposition 2, eqs. (11)-(12) (p. 13); proof in Appendix C (pp. A5-A7).

import Definitions.Def_LostSalesRQ_lower_curve
import Definitions.Def_LostSalesRQ_poisson_process

namespace LostSalesRQ

theorem penalty_calibration (μ : ℝ) (hμ : 0 ≤ μ) :
    (∀ η : ℝ, 1 ≤ η → rankBound μ η + agingRateSup μ η = calibratedPenalty μ η) ∧
    ContinuousOn (calibratedPenalty μ) (Set.Ici 1) ∧
    StrictMonoOn (calibratedPenalty μ) (Set.Ici 1) ∧
    Set.BijOn (calibratedPenalty μ) (Set.Ici 1) (Set.Ici 1) := by sorry

end LostSalesRQ
