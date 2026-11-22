-- Prove2me | Theorems.Thm_MasulloRH_HeightTwoScalar_theta_row_sound
-- name    : MasulloRH.HeightTwoScalar.theta_row_sound
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T20:05:09.446273+00:00
-- url     : https://prove2.me/theorems/657d52ee-2fbc-4861-877c-d0086dba561f
-- title:
--   Soundness of rational value and derivative enclosures for finite theta branches
-- statement:
--   Let $q$ be a theta-row certificate, let $b$ select its direct or reflected branch, and suppose its rational validity conditions hold. Supply the exponential endpoint inequalities specified by the row; the reflected branch additionally requires the two bounds for its prefactor $e^{-x}$.
--
--   Let $F_b$ denote the chosen finite theta model with truncation index $K=6$, and let $D_b$ be its explicit derivative expression, both defined in `MasulloRH_ThetaCertificate`. Then every $x$ in the row's interval $[q_{\rm left},q_{\rm right}]$ satisfies
--
--   $$q_{\rm value,L}\le F_b(x)\le q_{\rm value,U},\qquad q_{\rm deriv,L}\le D_b(x)\le q_{\rm deriv,U}.$$
--
--   The rational checks include the intermediate product, polynomial and moment-polynomial enclosures. The exponential inequalities remain explicit hypotheses, normally supplied by the separate exponential-certificate soundness theorem. This statement concerns finite branch models. Their comparison with the actual infinite theta function, and the branch restrictions needed for truncation-error bounds, are separate obligations.
-- source:
--   Reusable soundness theorem constructed for the independent theta-approximation branch of the Prove2Me Masullo RH specialization mission. It supports the exact eleven-term height-two certificate and uses the published MasulloRH_ThetaCertificate definitions. This is a new supporting construction, not a theorem attributed to a particular manuscript passage.

import Mathlib
import Definitions.Def_MasulloRH_ThetaCertificate
set_option autoImplicit false
open scoped BigOperators
open Set _root_.MasulloRH.CertifiedExp _root_.MasulloRH.Certificates
open _root_.MasulloRH.HeightTwoScalar

theorem MasulloRH.HeightTwoScalar.theta_row_sound
    (q : ThetaRow) (reflected : Bool) (hq : q.Valid reflected)
    (eiL : (q.iL : ℝ) ≤ Real.exp (q.iArgL : ℝ))
    (eiU : Real.exp (q.iArgU : ℝ) ≤ (q.iU : ℝ))
    (erL : (q.rL : ℝ) ≤ Real.exp (q.rArgL : ℝ))
    (erU : Real.exp (q.rArgU : ℝ) ≤ (q.rU : ℝ))
    (epref : reflected = true →
      (q.prefL : ℝ) ≤ Real.exp (q.prefArgL : ℝ) ∧
        Real.exp (q.prefArgU : ℝ) ≤ (q.prefU : ℝ)) :
    ∀ x ∈ Set.Icc (q.left : ℝ) (q.right : ℝ),
      ((q.valueL : ℝ) ≤ thetaBranchModel 6 reflected x ∧
        thetaBranchModel 6 reflected x ≤ (q.valueU : ℝ)) ∧
      ((q.derivL : ℝ) ≤ thetaBranchDerivative 6 reflected x ∧
        thetaBranchDerivative 6 reflected x ≤ (q.derivU : ℝ)) := by sorry
