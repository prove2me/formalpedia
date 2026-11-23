-- Prove2me | Theorems.Thm_NoHair_compact_ricci_deformation_lapse_flux_derivative
-- name    : NoHair.compact_ricci_deformation_lapse_flux_derivative
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T12:28:47.758654+00:00
-- url     : https://prove2.me/theorems/19a30020-2f5a-4d83-82fd-d5a02e63c7e9
-- title:
--   Conformal correction of a compact Ricci variation and its exact ADM lapse-flux derivative
-- statement:
--   For the metric variation $g_t=g-t\chi\operatorname{Ric}$, solve $-8\Delta_{g_t}u_t+R(g_t)u_t=0$ with $u_t\to1$ at infinity. The normalized lapse is $L_t=2u_t-1$. Since $R(g)=0$, integration of the differentiated equation and the compactly supported first variation of total scalar curvature give $F\prime(0)=(16\pi)^{-1}\int\chi|\operatorname{Ric}|_g^2dV_g$. The corrected scalar-flat metrics must be complete and retain the required ADM falloff.
-- source:
--   R. Schoen and S.-T. Yau, On the proof of the positive mass conjecture in general relativity, Comm. Math. Phys. 65 (1979), 45–76, https://doi.org/10.1007/BF01940959. R. Bartnik, The mass of an asymptotically flat manifold, Comm. Pure Appl. Math. 39 (1986), 661–693, https://doi.org/10.1002/cpa.3160390505.

import Definitions.Def_NoHair_spatialRicciEnergyDensity

open NoHair Set Filter Bundle MeasureTheory
open scoped ContDiff Manifold Topology

theorem NoHair.compact_ricci_deformation_lapse_flux_derivative (Q : Type) [m : MetricSpace Q] [ch : ChartedSpace ADMPoint Q] [sm : IsManifold 𝓘(ℝ,ADMPoint) ∞ Q]
    [rb : RiemannianBundle (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)]
    [sr : IsContMDiffRiemannianBundle 𝓘(ℝ,ADMPoint) ∞ ADMPoint (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)]
    [rm : IsRiemannianManifold 𝓘(ℝ,ADMPoint) Q] [cm : CompleteSpace Q] [cn : ConnectedSpace Q]
    [sc : SecondCountableTopology Q]
    (hend : HasScalarFlatZeroADMEnd Q)
    (e : OpenPartialHomeomorph Q ADMPoint) (he : e∈atlas ADMPoint Q) (χ : ADMPoint → ℝ)
    (nonnegative : 0≤χ) (smooth : ContDiff ℝ ∞ χ) (compact : HasCompactSupport χ) (interiorSupport : tsupport χ ⊆ e.target) :
    ∃ F : ℝ → ℝ, F 0 = 0 ∧ deriv F 0 = (∫ x : ADMPoint, χ x*spatialRicciEnergyDensity (riemannianEndCoeffs e.symm) x)/(16*Real.pi) ∧ ∀ᶠ t in 𝓝 (0:ℝ),
      ∃ (L : ADMPoint → ℝ) (g : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ) (mass : ℝ),
        HasStaticFirstOrderFalloff L g ∧ Tendsto (staticADMFlux g) atTop (𝓝 0) ∧
        Tendsto (staticLapseFlux L) atTop (𝓝 (F t)) ∧
        Tendsto (staticADMFlux (staticPositiveMetric L g)) atTop (𝓝 mass) ∧ IsScalarFlatADMMass mass := by sorry
