-- Prove2me | Theorems.Thm_NoHair_ricci_variation_conformal_lapse_flux
-- name    : NoHair.ricci_variation_conformal_lapse_flux
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T10:49:26.4527+00:00
-- url     : https://prove2.me/theorems/dddb9a62-b5f1-449f-9cf0-db4112318407
-- title:
--   Conformal scalar-flat deformation and first variation of its boundary flux
-- statement:
--   Perturb a zero-mass scalar-flat metric in the direction $-\chi\operatorname{Ric}$ on a compact patch with nonzero Ricci tensor. Solve $-8\Delta_{g_t}u_t+R(g_t)u_t=0$ with limit one. In the existing normalization $L_t=2u_t-1$, the lapse flux $F(t)$ vanishes at zero and has strictly positive derivative. The unrescaled metric retains mass zero, and the rescaling realizes a complete scalar-flat asymptotically flat metric. The conformal ADM transformation then determines its mass.
-- source:
--   R. Schoen and S.-T. Yau, On the proof of the positive mass conjecture in general relativity, Comm. Math. Phys. 65 (1979), 45–76, https://doi.org/10.1007/BF01940959. R. Bartnik, The mass of an asymptotically flat manifold, Comm. Pure Appl. Math. 39 (1986), 661–693, https://doi.org/10.1002/cpa.3160390505.

import Definitions.Def_NoHair_scalarFlatMassDeformation

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

theorem NoHair.ricci_variation_conformal_lapse_flux (Q : Type) [m : MetricSpace Q] [ch : ChartedSpace ADMPoint Q] [sm : IsManifold 𝓘(ℝ,ADMPoint) ∞ Q]
    [rb : RiemannianBundle (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)]
    [sr : IsContMDiffRiemannianBundle 𝓘(ℝ,ADMPoint) ∞ ADMPoint (fun q : Q => TangentSpace 𝓘(ℝ,ADMPoint) q)]
    [rm : IsRiemannianManifold 𝓘(ℝ,ADMPoint) Q] [cm : CompleteSpace Q] [cn : ConnectedSpace Q]
    [sc : SecondCountableTopology Q]
    (hend : HasScalarFlatZeroADMEnd Q)
    (hric : ¬ RicciFlatInADMCharts Q) :
    ∃ F : ℝ → ℝ, F 0 = 0 ∧ 0 < deriv F 0 ∧ ∀ᶠ t in 𝓝 (0:ℝ),
      ∃ (L : ADMPoint → ℝ) (g : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ) (mass : ℝ),
        HasStaticFirstOrderFalloff L g ∧ Tendsto (staticADMFlux g) atTop (𝓝 0) ∧
        Tendsto (staticLapseFlux L) atTop (𝓝 (F t)) ∧
        Tendsto (staticADMFlux (staticPositiveMetric L g)) atTop (𝓝 mass) ∧ IsScalarFlatADMMass mass := by sorry
