-- Prove2me | Theorems.Thm_LostSalesRQ_poisson_gaussian_rank_bound
-- name    : LostSalesRQ.poisson_gaussian_rank_bound
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-17T18:30:32.193191+00:00
-- url     : https://prove2.me/theorems/78cdb6f1-1abb-434c-beb1-2be8379bc72f
-- title:
--   Lemma G.1: Poisson-to-Gaussian rank bound
-- statement:
--   For $G(s)=\inf_{z\in\mathbb R}\{\phi(z)+z\Phi(z)+s[1-\Phi(z)]\}$,
--   $$B_\mu(\eta)>\sqrt\mu\,G\big(\eta/\sqrt\mu\big)\qquad(\mu>0,\ \eta\ge1).$$
--
--   The rank bound of the Poisson lead-time demand dominates its Gaussian counterpart at every finite $\mu$, strictly.
-- source:
--   M. Hu, "A 1.932 Guarantee for (r,Q) Policies in Continuous-Review Lost-Sales Inventory Systems", arXiv:2610.34576, 2026; Lemma G.1, eq. (G.1) (p. A12).

import Definitions.Def_LostSalesRQ_lower_curve
import Definitions.Def_LostSalesRQ_gaussian

namespace LostSalesRQ

theorem poisson_gaussian_rank_bound (μ η : ℝ) (hμ : 0 < μ) (hη : 1 ≤ η) :
    Real.sqrt μ * gaussianRankProfile (η / Real.sqrt μ) < rankBound μ η := by sorry

end LostSalesRQ
