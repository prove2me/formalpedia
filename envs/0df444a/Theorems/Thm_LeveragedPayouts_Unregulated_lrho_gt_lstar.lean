-- Prove2me | Theorems.Thm_LeveragedPayouts_Unregulated_lrho_gt_lstar
-- name    : LeveragedPayouts.Unregulated.lrho_gt_lstar
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:24:20.29718+00:00
-- url     : https://prove2.me/theorems/69a20be7-d277-4102-9aa2-287a76098ff6
-- title:
--   Proof of Proposition 9, p. 26 — the first-best date-0 labour l_ρ exceeds l*, and the wage w_ρ = ρg′(1 − l_ρ) is below w*
-- statement:
--   In the economy of the mission, let $\rho\in(0,1)$ be the date-0 productivity shock and let $l_\rho\in(0,1)$ be the first-best date-0 labour, $\pi f'(l_\rho)/(2R)=\rho g'(1-l_\rho)$. Then
--   $$l_\rho>l^*\qquad\text{and}\qquad w_\rho:=\rho\,g'(1-l_\rho)<w^* .$$
--
--   When the date-0 consumption-good sector is less productive, the efficient allocation moves labour into the capital-good sector and lowers the flexible wage; the downward-rigid wage $w^*$ prevents this, which is the friction monetary policy tries to offset.
--
--   **Formalization Note** $w_\rho$ is the flexible date-0 wage given by (27) with $g_0=\rho g$.
-- source:
--   Acharya & Plantin, Monetary Easing, Leveraged Payouts, and Lack of Investment, SSRN 3484935 (version of May 23, 2023), p. 26, proof of Proposition 9, (26)–(28)

import Mathlib
import Definitions.Def_LeveragedPayouts_Unregulated_Setting

namespace LeveragedPayouts.Unregulated
theorem lrho_gt_lstar (E : Economy) (ρ lρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hlρ : IsFirstBestLabor E ρ lρ) :
    E.lstar < lρ ∧ ρ * deriv E.g (1 - lρ) < E.wstar := by sorry
end LeveragedPayouts.Unregulated
