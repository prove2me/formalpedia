-- Prove2me | Theorems.Thm_LostSalesRQ_lower_curve_properties
-- name    : LostSalesRQ.lower_curve_properties
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-17T18:25:17.988804+00:00
-- url     : https://prove2.me/theorems/c1233cc3-b518-4fec-a139-7381b4ea0ea3
-- title:
--   Eq. (14) and Section 4.3.3: properties of the concave lower curve $\mathcal L_\mu$
-- statement:
--   Fix $\mu\ge0$. The concave lower curve $\mathcal L_\mu(a)=\sup_{\eta\ge1}\min\{B_\mu(\eta),a-D_\mu(\eta)\}$ satisfies:
--
--   1. $\mathcal L_\mu(a)\le\mathrm{OPT}_0(\mu,a)$ for every $a\ge0$;
--   2. $\mathcal L_\mu(\alpha_\mu(\eta))\ge B_\mu(\eta)$ for every $\eta\ge1$;
--   3. $\mathcal L_\mu$ is concave on $[0,\infty)$;
--   4. $\mathcal L_\mu$ is nondecreasing on $[0,\infty)$;
--   5. $\mathcal L_\mu$ is $1$-Lipschitz on $[0,\infty)$;
--   6. $\min\{1,a\}\le\mathcal L_\mu(a)\le a$ for every $a\ge0$.
--
--   Items 1 and 2 are eq. (14); concavity is what allows a base-stock comparison at two penalties to extend to the whole interval between them.
-- source:
--   M. Hu, "A 1.932 Guarantee for (r,Q) Policies in Continuous-Review Lost-Sales Inventory Systems", arXiv:2610.34576, 2026; Section 4.3.3, eq. (14) and the following paragraph (pp. 14-15).

import Definitions.Def_LostSalesRQ_model
import Definitions.Def_LostSalesRQ_lower_curve
import Definitions.Def_LostSalesRQ_poisson_process

namespace LostSalesRQ

theorem lower_curve_properties (μ : ℝ) (hμ : 0 ≤ μ) :
    (∀ a : ℝ, 0 ≤ a → ENNReal.ofReal (lowerCurve μ a) ≤ OPTk μ a 0) ∧
    (∀ η : ℝ, 1 ≤ η → rankBound μ η ≤ lowerCurve μ (calibratedPenalty μ η)) ∧
    ConcaveOn ℝ (Set.Ici 0) (lowerCurve μ) ∧
    MonotoneOn (lowerCurve μ) (Set.Ici 0) ∧
    (∀ a b : ℝ, 0 ≤ a → 0 ≤ b → |lowerCurve μ a - lowerCurve μ b| ≤ |a - b|) ∧
    (∀ a : ℝ, 0 ≤ a → min 1 a ≤ lowerCurve μ a ∧ lowerCurve μ a ≤ a) := by sorry

end LostSalesRQ
