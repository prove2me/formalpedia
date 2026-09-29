-- Prove2me | Theorems.Thm_LambdaCDM_exists_frwUniverse
-- name    : LambdaCDM.exists_frwUniverse
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T03:02:09.882998+00:00
-- url     : https://prove2.me/theorems/bce18f9a-13f6-4381-8c5b-5fc4cfe27a19
-- title:
--   The closed form is an FRW universe with dust and a cosmological constant
-- statement:
--   Fix flat ΛCDM parameters and any Newton constant $G>0$. Then there is an FRW universe in the sense of the published FRW model — a spatially homogeneous isotropic solution consisting of a gravitational constant, a curvature constant $K$, an open connected time domain $I$, a positive scale factor together with its first two derivatives, an energy density with its derivative, and a pressure, all subject pointwise on $I$ to the two Friedmann equations
--   $$\left(\frac{\dot a}{a}\right)^2=\frac{8\pi G}{3}\rho-\frac{K}{a^2},\qquad \frac{\ddot a}{a}-\left(\frac{\dot a}{a}\right)^2=-4\pi G(\rho+p)+\frac{K}{a^2}$$
--   — whose gravitational constant is $G$, whose curvature vanishes, whose time domain is $(0,\infty)$, whose scale factor is the ΛCDM closed form $a(t)=(\Omega_m/\Omega_\Lambda)^{1/3}\sinh^{2/3}(\tfrac32\sqrt{\Omega_\Lambda}H_0t)$, and whose density and pressure are, for $t>0$,
--   $$\rho(t)=\frac{3H_0^2}{8\pi G}\left(\frac{\Omega_m}{a(t)^3}+\Omega_\Lambda\right),\qquad p(t)=-\frac{3H_0^2}{8\pi G}\,\Omega_\Lambda.$$
--   In other words the closed form, with pressureless matter diluting as $a^{-3}$ plus a constant dark-energy density of equation of state $w=-1$, satisfies both Friedmann equations, not only the first.
-- source:
--   Wikipedia, Lambda-CDM model, https://en.wikipedia.org/wiki/Lambda-CDM_model, section 'Cosmic expansion history' (Friedmann equation in density parameters, closed-form solution a(t), age t0, deceleration-to-acceleration transition)

import Mathlib
import Definitions.Def_FlatLambdaCDM
import Definitions.Def_FRWUniverse

namespace LambdaCDM

theorem exists_frwUniverse (P : FlatLCDM) (G : ℝ) (hG : 0 < G) :
    ∃ U : FRWCosmology.FRWUniverse,
      U.G = G ∧ U.K = 0 ∧ U.I = Set.Ioi 0 ∧ U.a = scaleFactor P ∧
      (∀ t ∈ U.I, U.rho t = 3 * P.H0 ^ 2 / (8 * Real.pi * G) *
        (P.Om / scaleFactor P t ^ 3 + P.OL)) ∧
      (∀ t ∈ U.I, U.p t = -(3 * P.H0 ^ 2 / (8 * Real.pi * G)) * P.OL) := by sorry

end LambdaCDM
