-- Prove2me | Theorems.Thm_OAI_ScalarConductivity_attachedPeriodicFlux_smooth_green
-- name    : OAI.ScalarConductivity.attachedPeriodicFlux_smooth_green
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T21:57:07.569992+00:00
-- url     : https://prove2.me/theorems/886e10da-08ff-429e-9965-a1d13f009a0f
-- title:
--   OAI.ScalarConductivity.attachedPeriodicFlux_smooth_green: intermediate lemma from OpenAI, Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.ScalarConductivity.main_nonuniqueness`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365)*, OpenAI Math Release, September 23, 2026, result family 365, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.ScalarConductivity.attachedPeriodicFlux_smooth_green` of [lean/OAI/Analysis/Conductivity/Fourier/AttachedPeriodicGreen.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Conductivity/Fourier/AttachedPeriodicGreen.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.ScalarConductivity`, with `open Set Filter Topology MeasureTheory UnitAddTorus Matrix`, `open scoped ENNReal`):
--
--   ```lean
--   theorem attachedPeriodicFlux_smooth_green {F : Coord3 → Coord3}
--       (hF : ContDiff ℝ 1 F) (hp : AngularPeriodic (2*Real.pi) F)
--       {φ : Coord3 → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ)
--       {a b l r R : ℝ} (ha : a≠0) (hlr : l ≤ r) (hR : 0≤R)
--       (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
--       (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R)
--       (he : (0<a ∧ a*(l-b)=0 ∧ a*(r-b)=R) ∨
--         (a<0 ∧ a*(l-b)=R ∧ a*(r-b)=0))
--       (hd : ∀ x,x 0∈Icc 0 R → coordinateDivergence F x=0) :
--       IntegrableOn (fun y => attachedPeriodicFlux F a b y ⬝ᵥphysicalTestCovector φ y)
--         (sourceClosedCollarBand l r) volume ∧
--       (∫ y in sourceClosedCollarBand l r,attachedPeriodicFlux F a b y ⬝ᵥphysicalTestCovector φ y)=
--         angularArea*((∫ θ,torusPeriodicDescent F (R,θ) 0*
--             φ (sourceAngularCollar (a⁻¹*R+b) θ))-
--           (∫ θ,torusPeriodicDescent F (0,θ) 0*φ (sourceAngularCollar b θ)))
--   ```
--
--   **Definitions.** The statement is written with `OAI.ScalarConductivity.AngularPeriodic`, `OAI.ScalarConductivity.Coord3`, `OAI.ScalarConductivity.angularArea`, `OAI.ScalarConductivity.coordinateDivergence`, `OAI.ScalarConductivity.sourceAngularCollar` and `OAI.ScalarConductivity.sourceClosedCollarBand` (definitions bundle `OAIQ059C000` of this split); `OAI.ScalarConductivity.affineEndTime`, `OAI.ScalarConductivity.attachedPeriodicGreenMeasureSpace` and `OAI.ScalarConductivity.physicalTestCovector` (definitions bundle `OAIQ059C001` of this split); `OAI.ScalarConductivity.torusPeriodicDescent` (definitions bundle `OAIQ059C004` of this split); `OAI.ScalarConductivity.attachedPeriodicFlux` (definitions bundle `OAIQ059C006` of this split).
--
--   **Used by.** The proof of `OAI.ScalarConductivity.PhysicalFiniteEndingData.corrected_block_smooth_green` of this split imports it.
-- source:
--   OpenAI, Nonuniqueness for bounded measurable scalar conductivities in three dimensions (result family 365), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 365; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Nonuniqueness-for-Bounded-Measurable-Scalar-Conductivities-in-Three-Dimensions-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Conductivity/Fourier/AttachedPeriodicGreen.lean (declaration OAI.ScalarConductivity.attachedPeriodicFlux_smooth_green)

import Mathlib
import Definitions.Def_OAIQ059C006

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

noncomputable section
namespace ScalarConductivity
open Set Filter Topology MeasureTheory UnitAddTorus Matrix
open scoped ENNReal

attribute [local instance] OAI.ScalarConductivity.attachedPeriodicGreenMeasureSpace
local instance attachedPeriodicGreenIsProbabilityMeasure_r0bcb51_1 : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)
theorem attachedPeriodicFlux_smooth_green {F : Coord3 → Coord3}
    (hF : ContDiff ℝ 1 F) (hp : AngularPeriodic (2*Real.pi) F)
    {φ : Coord3 → ℝ} (hφ : ContDiff ℝ (↑(⊤:ℕ∞)) φ)
    {a b l r R : ℝ} (ha : a≠0) (hlr : l ≤ r) (hR : 0≤R)
    (hl : -(1:ℝ)/100≤l) (hr : r≤1/100)
    (hT : ∀ t∈Icc l r,affineEndTime a b t∈Icc 0 R)
    (he : (0<a ∧ a*(l-b)=0 ∧ a*(r-b)=R) ∨
      (a<0 ∧ a*(l-b)=R ∧ a*(r-b)=0))
    (hd : ∀ x,x 0∈Icc 0 R → coordinateDivergence F x=0) :
    IntegrableOn (fun y => attachedPeriodicFlux F a b y ⬝ᵥphysicalTestCovector φ y)
      (sourceClosedCollarBand l r) volume ∧
    (∫ y in sourceClosedCollarBand l r,attachedPeriodicFlux F a b y ⬝ᵥphysicalTestCovector φ y)=
      angularArea*((∫ θ,torusPeriodicDescent F (R,θ) 0*
          φ (sourceAngularCollar (a⁻¹*R+b) θ))-
        (∫ θ,torusPeriodicDescent F (0,θ) 0*φ (sourceAngularCollar b θ))) := by
  sorry

end ScalarConductivity

end
end

end OAI
end
