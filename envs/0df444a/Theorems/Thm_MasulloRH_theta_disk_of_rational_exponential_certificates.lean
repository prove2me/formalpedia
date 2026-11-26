-- Prove2me | Theorems.Thm_MasulloRH_theta_disk_of_rational_exponential_certificates
-- name    : MasulloRH.theta_disk_of_rational_exponential_certificates
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T09:57:42.455197+00:00
-- url     : https://prove2.me/theorems/10e225d5-068d-483f-b318-5bf658e2cb43
-- title:
--   Complex theta disks from four rational exponential rows
-- statement:
--   Four published rational exponential certificate rows can enclose the nested Gaussian parameter \(q(z)=\exp(-\pi(e^z)^2)\). The first two rows enclose \(e^w\); the other two bound the exponential between the resulting negative-product endpoints. A positive rational divisor \(d\) allows \(d(e^z)^2=e^w\). Direct cells use \(d=1, w=2z\). Reflected cells at an original coordinate \(x\) use \(z=-x-\log4\), \(w=-2x\) and \(d=16\).
--
--   Writing \(L,U\) for the resulting parameter endpoints, use the sign-sensitive degree-indexed polynomial \(B(a,b)=2\sum_{k=1}^K(a^{k^2}-3b^{4k^2}+2a^{16k^2})\) and tail bound \(E=12U^{(K+1)^2}/(1-U^{2K+3})\). If rational arithmetic checks \([B(L,U)-E,B(U,L)+E]\subseteq[C-R,C+R]\), then the full canonical complex theta value satisfies \(\lVert\theta(z)-C\rVert\le R\) throughout the indicated input interval.
-- source:
--   Developed for the central height-two grid, https://prove2.me/theorems/44743777-9b41-5194-84da-ff2782e96168 . The underlying rational row format is https://prove2.me/definitions/55b584ef-23cf-4152-bb89-68f7cb944cd5 .

import Definitions.Def_MasulloRH_ThetaCertificate
import Definitions.Def_MasulloRH_GaussianThetaApproximation

open MasulloRH.GaussianApproximation MasulloRH.HeightTwoScalar
open scoped BigOperators
set_option autoImplicit false

theorem MasulloRH.theta_disk_of_rational_exponential_certificates (K : ℕ) (iL iU qL qU : ExpRow) (d C R : ℚ)
    (hrows : iL.Valid ∧ iU.Valid ∧ qL.Valid ∧ qU.Valid)
    (hd : 0 < d) (hi : 0 ≤ iL.lower)
    (ha : qL.argument*d ≤ -piUpperQ*iU.upper ∧
          -piLowerQ*iL.lower ≤ qU.argument*d)
    (hq : 0 ≤ qL.lower ∧ qU.upper < 1)
    (hwin : let B (a b : ℚ) := 2 * ∑ n ∈ Finset.range K,
               (a^((n+1)^2) - 3*b^(4*(n+1)^2) + 2*a^(16*(n+1)^2))
            let E := 12*qU.upper^((K+1)^2)/(1-qU.upper^(2*K+3))
            C-R ≤ B qL.lower qU.upper-E ∧ B qU.upper qL.lower+E ≤ C+R)
    (z w : ℝ) (hw : (iL.argument : ℝ) ≤ w ∧ w ≤ (iU.argument : ℝ))
    (hz : (Real.exp z)^2 * (d:ℝ) = Real.exp w) :
    ‖theta z - (C : ℂ)‖ ≤ (R : ℝ) := by sorry
