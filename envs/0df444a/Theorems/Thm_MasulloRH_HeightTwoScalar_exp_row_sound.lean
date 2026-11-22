-- Prove2me | Theorems.Thm_MasulloRH_HeightTwoScalar_exp_row_sound
-- name    : MasulloRH.HeightTwoScalar.exp_row_sound
-- status  : Proved
-- author  : @sflicht
-- created : 2026-11-21T20:05:07.659475+00:00
-- url     : https://prove2.me/theorems/ce80ca98-8942-4d4b-99cc-fbd5fadce7de
-- title:
--   Soundness of exact rational exponential certificates
-- statement:
--   Let $q$ be a rational exponential certificate from `MasulloRH_ThetaCertificate`, with rational argument $t$ and proposed rational endpoints $\ell,u$. If its exact rational validity conditions hold, then
--
--   $$\ell\le e^t\le u.$$
--
--   The four supported certificate methods are the value at zero, positive Taylor scaling, negative Taylor scaling through reciprocal bounds, and an integer-power upper bound for a negative argument. For the Taylor methods the certificate includes a reduced argument in $[0,1]$, a positive truncation order, explicit rational Taylor-remainder bounds, and the rational scaling inequalities. For the last method it includes an integer $n\ge0$ with $n\le-t$, $\ell\le0$, and $2^{-n}\le u$. Unsupported methods fail the validity predicate.
--
--   This is a soundness theorem for a rational checker. It does not assume the desired real exponential enclosure and does not rely on a floating-point evaluator.
-- source:
--   Reusable soundness theorem constructed for the independent theta-approximation branch of the Prove2Me Masullo RH specialization mission. It supports the exact eleven-term height-two certificate and uses the published MasulloRH_ThetaCertificate definitions. This is a new supporting construction, not a theorem attributed to a particular manuscript passage.

import Mathlib
import Definitions.Def_MasulloRH_ThetaCertificate
set_option autoImplicit false
open scoped BigOperators
open Set _root_.MasulloRH.CertifiedExp _root_.MasulloRH.Certificates
open _root_.MasulloRH.HeightTwoScalar

theorem MasulloRH.HeightTwoScalar.exp_row_sound (q : ExpRow) (hq : q.Valid) :
    (q.lower : ℝ) ≤ Real.exp (q.argument : ℝ) ∧
      Real.exp (q.argument : ℝ) ≤ (q.upper : ℝ) := by sorry
