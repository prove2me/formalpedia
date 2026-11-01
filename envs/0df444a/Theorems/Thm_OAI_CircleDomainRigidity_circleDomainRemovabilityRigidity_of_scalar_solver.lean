-- Prove2me | Theorems.Thm_OAI_CircleDomainRigidity_circleDomainRemovabilityRigidity_of_scalar_solver
-- name    : OAI.CircleDomainRigidity.circleDomainRemovabilityRigidity_of_scalar_solver
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-01T05:39:07.990038+00:00
-- url     : https://prove2.me/theorems/65fe268d-7b02-4919-9846-840f4158dc28
-- title:
--   OAI.CircleDomainRigidity.circleDomainRemovabilityRigidity_of_scalar_solver: intermediate lemma from OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem047.koebe_circle_domain` and `OAI.Problem047.removability_implies_rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Koebe's circle-domain conjecture and rigidity (result family 71)*, OpenAI Math Release, September 23, 2026, result family 71, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CircleDomainRigidity.circleDomainRemovabilityRigidity_of_scalar_solver` of [lean/OAI/Analysis/CircleDomains/Rigidity/ConditionalRigidity.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/CircleDomains/Rigidity/ConditionalRigidity.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CircleDomainRigidity`, with `open Set Function Filter MeasureTheory`, `open scoped Topology ENNReal NNReal ContDiff`, `open FiniteTransfer`):
--
--   ```lean
--   theorem circleDomainRemovabilityRigidity_of_scalar_solver
--       (hmax : PlanarMaximalL2)
--       (hsolver : PrincipalConductivityScalarSolver) (hprincipal : PrincipalRealBeltrami)
--       (hsob : PlanarSobolevCoarea)
--       (hcross : UnitDiskAlternatingContinua)
--       (hplane : PlanarLipschitzFiberCoarea)
--       (hcoarea : WeightedPlanarScalarCoarea) (hLusin : FiniteTorusAnalyticMeasurability)
--       (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
--       (hcollar : SmoothRegularJordanCollars) (hselect : BorelPathRelationSelection)
--       (hgreen : UnorientedFiniteCircleGreenFormula) (harea : ExteriorCoefficientAreaTheorem)
--       (hcompact : SmoothCompactMetricSphereUniformization) (hfinite : FiniteJordanModelUniformization)
--       (hmontel : MontelExhaustion) (hhurwitz : HurwitzUnivalentLimit) (hzero : HurwitzZeroFreeLimit)
--       (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
--         HasSimpleArcsInConnectedOpens C)
--       (hstandard : ∀ e : PathCodeData Sphere Sphere, [StandardBorelSpace (BasePathCode e)] →
--         StandardBorelProbabilityLaws (BasePathCode e))
--       (hpath : PolishProbabilityLaws C(PathTime, Sphere))
--       (hdual : ∀ (e : PathCodeData Sphere Sphere)
--         (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
--         (ν : Measure Sphere) [IsFiniteMeasure ν]
--         [StandardBorelSpace (ConstrainedCostCode e b c ν)],
--         MeasureImageDuality (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
--       (hlift : ∀ (e : PathCodeData Sphere Sphere)
--         (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
--         (ν : Measure Sphere) [IsFiniteMeasure ν]
--         [StandardBorelSpace (ConstrainedCostCode e b c ν)],
--         MeasurePlanLifting (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
--       (hareaBound : ExteriorOmittedAreaTheorem)
--       : CircleDomainRemovabilityRigidity
--   ```
--
--   **Definitions.** The statement is written with `OAI.CircleDomainRigidity.PathCodeData`, `OAI.CircleDomainRigidity.PathTime`, `OAI.CircleDomainRigidity.PlanarSchoenflies`, `OAI.CircleDomainRigidity.SmoothPlanarSard`, `OAI.CircleDomainRigidity.TagSlot`, `OAI.CircleDomainRigidity.TaggedPath`, `OAI.CircleDomainRigidity.residualImage`, `OAI.CircleDomainRigidity.sphereBorel` and `OAI.CircleDomainRigidity.sphereMetric` (definitions bundle `Q146C001` of this split); `OAI.CircleDomainRigidity.ExteriorCoefficientAreaTheorem`, `OAI.CircleDomainRigidity.ExteriorOmittedAreaTheorem`, `OAI.CircleDomainRigidity.FiniteTorusAnalyticMeasurability`, `OAI.CircleDomainRigidity.HasSimpleArcsInConnectedOpens`, `OAI.CircleDomainRigidity.HurwitzUnivalentLimit`, `OAI.CircleDomainRigidity.HurwitzZeroFreeLimit`, `OAI.CircleDomainRigidity.MeasureImageDuality`, `OAI.CircleDomainRigidity.MeasurePlanLifting`, `OAI.CircleDomainRigidity.MontelExhaustion`, `OAI.CircleDomainRigidity.PathCostSpace`, `OAI.CircleDomainRigidity.PlanarLipschitzFiberCoarea`, `OAI.CircleDomainRigidity.PlanarMaximalL2`, `OAI.CircleDomainRigidity.PolishProbabilityLaws`, `OAI.CircleDomainRigidity.StandardBorelProbabilityLaws`, `OAI.CircleDomainRigidity.UnitDiskAlternatingContinua`, `OAI.CircleDomainRigidity.WeightedPlanarScalarCoarea`, `OAI.CircleDomainRigidity.instBorelSpacePathCostSpace`, `OAI.CircleDomainRigidity.instMeasurableSpacePathCostSpaceOfTopologicalSpace`, `OAI.CircleDomainRigidity.instPolishSpacePathCostSpace` and `OAI.CircleDomainRigidity.instTopologicalSpacePathCostSpace` (definitions bundle `Q146C002` of this split); `OAI.CircleDomainRigidity.BasePathCode`, `OAI.CircleDomainRigidity.BorelPathRelationSelection`, `OAI.CircleDomainRigidity.CircleDomainRemovabilityRigidity`, `OAI.CircleDomainRigidity.ConstrainedCostCode`, `OAI.CircleDomainRigidity.EndpointCode`, `OAI.CircleDomainRigidity.FiniteCostCode`, `OAI.CircleDomainRigidity.FiniteJordanModelUniformization`, `OAI.CircleDomainRigidity.instMeasurableSpaceTagSlot` and `OAI.CircleDomainRigidity.pathCostMeasure` (definitions bundle `Q146C004` of this split); `OAI.CircleDomainRigidity.PlanarSobolevCoarea`, `OAI.CircleDomainRigidity.PrincipalRealBeltrami`, `OAI.CircleDomainRigidity.UnitDiskCrosscutSeparation`, `OAI.CircleDomainRigidity.UnorientedFiniteCircleGreenFormula` and `OAI.CircleDomainRigidity.instBorelSpaceSphere_80` (definitions bundle `Q146C005` of this split); `OAI.CircleDomainRigidity.PrincipalConductivityScalarSolver` and `OAI.CircleDomainRigidity.SmoothCompactMetricSphereUniformization` (definitions bundle `Q146C008` of this split); `OAI.CircleDomainRigidity.SmoothRegularJordanCollars` (definitions bundle `Q146C010` of this split); `OAI.CircleDomainRigidity.Sphere` (the published bundle `Def_KoebeCircleDomains`).
--
--   **Used by.** The proof of `OAI.Problem047.removability_implies_rigidity` of this split imports it.
-- source:
--   OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 71; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Koebes-Circle-Domain-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/CircleDomains/Rigidity/ConditionalRigidity.lean (declaration OAI.CircleDomainRigidity.circleDomainRemovabilityRigidity_of_scalar_solver)

import Mathlib
import Definitions.Def_KoebeCircleDomains
import Definitions.Def_Q146C010

section

attribute [-instance] _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Function Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]

 attribute [local instance] OAI.CircleDomainRigidity.instBorelSpaceSphere_80
theorem circleDomainRemovabilityRigidity_of_scalar_solver
    (hmax : PlanarMaximalL2)
    (hsolver : PrincipalConductivityScalarSolver) (hprincipal : PrincipalRealBeltrami)
    (hsob : PlanarSobolevCoarea)
    (hcross : UnitDiskAlternatingContinua)
    (hplane : PlanarLipschitzFiberCoarea)
    (hcoarea : WeightedPlanarScalarCoarea) (hLusin : FiniteTorusAnalyticMeasurability)
    (hsard : SmoothPlanarSard) (hsch : PlanarSchoenflies) (hsep : UnitDiskCrosscutSeparation)
    (hcollar : SmoothRegularJordanCollars) (hselect : BorelPathRelationSelection)
    (hgreen : UnorientedFiniteCircleGreenFormula) (harea : ExteriorCoefficientAreaTheorem)
    (hcompact : SmoothCompactMetricSphereUniformization) (hfinite : FiniteJordanModelUniformization)
    (hmontel : MontelExhaustion) (hhurwitz : HurwitzUnivalentLimit) (hzero : HurwitzZeroFreeLimit)
    (harcs : ∀ C : Set Sphere, IsCompact C → LocallyConnectedSpace C →
      HasSimpleArcsInConnectedOpens C)
    (hstandard : ∀ e : PathCodeData Sphere Sphere, [StandardBorelSpace (BasePathCode e)] →
      StandardBorelProbabilityLaws (BasePathCode e))
    (hpath : PolishProbabilityLaws C(PathTime, Sphere))
    (hdual : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasureImageDuality (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    (hlift : ∀ (e : PathCodeData Sphere Sphere)
      (I : Set ℕ) [PolishSpace I] (b : I → Sphere) (c : I → ℝ≥0∞)
      (ν : Measure Sphere) [IsFiniteMeasure ν]
      [StandardBorelSpace (ConstrainedCostCode e b c ν)],
      MeasurePlanLifting (ConstrainedCostCode e b c ν) (PathCostSpace Sphere I))
    (hareaBound : ExteriorOmittedAreaTheorem)
    : CircleDomainRemovabilityRigidity := by
  sorry

end CircleDomainRigidity

end

end OAI
end
