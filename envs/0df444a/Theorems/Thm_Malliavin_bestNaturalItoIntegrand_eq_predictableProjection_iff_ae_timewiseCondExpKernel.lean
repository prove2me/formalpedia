-- Prove2me | Theorems.Thm_Malliavin_bestNaturalItoIntegrand_eq_predictableProjection_iff_ae_timewiseCondExpKernel
-- name    : Malliavin.bestNaturalItoIntegrand_eq_predictableProjection_iff_ae_timewiseCondExpKernel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:46:56.96283+00:00
-- url     : https://prove2.me/theorems/bfbdcc42-3446-457b-8805-1ba748c6ebbb
-- title:
--   Malliavin: best Natural Ito Integrand eq predictable Projection iff ae timewise Cond Exp Kernel
-- statement:
--   For the natural Brownian filtration, the raw timewise conditional-kernel formula required
--   by `ClarkOconeFamily.ofNaturalItoTimewiseCondExpKernel` is equivalent to the canonical
--   best-integrand equality required by `ClarkOconeFamily.ofNaturalItoBestIntegrand`.
--
--   Thus the global kernel identification supplies the jointly predictable representative of the
--   right-hand side, but does not by itself prove that the inverse-Itô integrand is that
--   representative.
--
--   Source: https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalClarkOcone.lean#L731-L764
-- source:
--   https://github.com/savarin/lean-malliavin/blob/a1a6ccc6eedbdf15fc3aebf9146d1fddfa0c8272/Malliavin/NaturalClarkOcone.lean#L731-L764

import Definitions.Def_Malliavin_KernelIdentification
import Definitions.Def_Malliavin_NaturalClarkOcone
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal InnerProductSpace
noncomputable section
open Malliavin
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
  [CompleteSpace W] [MeasurableSpace W] [BorelSpace W]
  [SecondCountableTopology W]
  {P : Measure W} [IsGaussian P]
  {B : ℝ≥0 → W → ℝ}

theorem Malliavin.bestNaturalItoIntegrand_eq_predictableProjection_iff_ae_timewiseCondExpKernel
    (hB : IsPreBrownianReal B P) (coordinate : ℝ≥0 → StrongDual ℝ W)
    (coordinate_apply : ∀ t w, B t w = coordinate t w)
    (generated : IsWienerGenerated B)
    (hsm : ∀ t, StronglyMeasurable (B t))
    {𝓅 : Filtration ℝ≥0 ‹MeasurableSpace W›}
    (hnat : 𝓅 = Filtration.natural B hsm) (F : D12 P) :
    bestNaturalItoIntegrand hB hsm hnat (centeredPartL2 F.1) =
        predictableProjection 𝓅
          (Malliavin.timeDerivative hB coordinate coordinate_apply generated
            (mderivD12 P F)) ↔
      ∀ᵐ t ∂nonnegativeLebesgueMeasure,
        (fun w ↦
          (bestNaturalItoIntegrand hB hsm hnat (centeredPartL2 F.1) :
            ℝ≥0 × W → ℝ) (t, w)) =ᵐ[P]
          fun w ↦ ∫ w',
            (Malliavin.timeDerivative hB coordinate coordinate_apply generated
              (mderivD12 P F) : ℝ≥0 × W → ℝ) (t, w')
            ∂condExpKernel P (𝓅 t) w := by sorry
