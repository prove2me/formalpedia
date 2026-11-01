-- Prove2me | Theorems.Thm_OAI_CircleDomainRigidity_MatchedConformalEnds_MatchedRealMask_global_sobolev_of_published_inputs
-- name    : OAI.CircleDomainRigidity.MatchedConformalEnds.MatchedRealMask.global_sobolev_of_published_inputs
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-01T05:33:50.658434+00:00
-- url     : https://prove2.me/theorems/c94d5d47-f014-44e4-ae7e-e46ca40521e5
-- title:
--   OAI.CircleDomainRigidity.MatchedConformalEnds.MatchedRealMask.global_sobolev_of_published_inputs: intermediate lemma from OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem047.koebe_circle_domain` and `OAI.Problem047.removability_implies_rigidity`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Koebe's circle-domain conjecture and rigidity (result family 71)*, OpenAI Math Release, September 23, 2026, result family 71, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CircleDomainRigidity.MatchedConformalEnds.MatchedRealMask.global_sobolev_of_published_inputs` of [lean/OAI/Analysis/CircleDomains/Rigidity/MatchedMaskGlobalSobolev.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/CircleDomains/Rigidity/MatchedMaskGlobalSobolev.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CircleDomainRigidity.MatchedConformalEnds`, with `open Set Function Filter MeasureTheory Metric`, `open scoped Topology ENNReal NNReal`, `open FiniteTransfer`):
--
--   ```lean
--   theorem MatchedRealMask.global_sobolev_of_published_inputs
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
--       {E : D.MatchedRoundDisks} {hG : IsOpen G} {hf : IsConformalEquivalence f G (f '' G)}
--       {φ : Sphere → ℝ} {L : ℝ≥0} {m : ℕ} (M : MatchedRealMask E hG hf φ L m)
--       (hinf : OnePoint.infty ∈ G)
--       (hb : ContDiffOn ℝ 1 (D.realSelectedScalar hG hf φ) (realPlaneDomain G))
--       (hb2 : MemLp (fderiv ℝ (D.realSelectedScalar hG hf φ)) 2 (volume.restrict (realPlaneDomain G))) :
--       Nonempty (DeGiorgi.MemW1pWitness 2
--         (D.realMaskValue E hG hf φ L M.cutoff ∘ euclideanPlaneCoordinates) univ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CircleDomainRigidity.EuclideanPlane`, `OAI.CircleDomainRigidity.PathCodeData`, `OAI.CircleDomainRigidity.PathTime`, `OAI.CircleDomainRigidity.PlanarSchoenflies`, `OAI.CircleDomainRigidity.SmoothPlanarSard`, `OAI.CircleDomainRigidity.TagSlot`, `OAI.CircleDomainRigidity.TaggedPath`, `OAI.CircleDomainRigidity.euclideanPlaneCoordinates`, `OAI.CircleDomainRigidity.residualImage`, `OAI.CircleDomainRigidity.sphereBorel`, `OAI.CircleDomainRigidity.sphereMetric` and `OAI.DeGiorgi.MemW1pWitness` (definitions bundle `Q146C001` of this split); `OAI.CircleDomainRigidity.ExteriorCoefficientAreaTheorem`, `OAI.CircleDomainRigidity.FiniteTorusAnalyticMeasurability`, `OAI.CircleDomainRigidity.HasSimpleArcsInConnectedOpens`, `OAI.CircleDomainRigidity.HurwitzUnivalentLimit`, `OAI.CircleDomainRigidity.HurwitzZeroFreeLimit`, `OAI.CircleDomainRigidity.MeasureImageDuality`, `OAI.CircleDomainRigidity.MeasurePlanLifting`, `OAI.CircleDomainRigidity.MontelExhaustion`, `OAI.CircleDomainRigidity.PathCostSpace`, `OAI.CircleDomainRigidity.PlanarLipschitzFiberCoarea`, `OAI.CircleDomainRigidity.PolishProbabilityLaws`, `OAI.CircleDomainRigidity.StandardBorelProbabilityLaws`, `OAI.CircleDomainRigidity.UnitDiskAlternatingContinua`, `OAI.CircleDomainRigidity.WeightedPlanarScalarCoarea`, `OAI.CircleDomainRigidity.instBorelSpacePathCostSpace`, `OAI.CircleDomainRigidity.instMeasurableSpacePathCostSpaceOfTopologicalSpace`, `OAI.CircleDomainRigidity.instPolishSpacePathCostSpace` and `OAI.CircleDomainRigidity.instTopologicalSpacePathCostSpace` (definitions bundle `Q146C002` of this split); `OAI.CircleDomainRigidity.BasePathCode`, `OAI.CircleDomainRigidity.BorelPathRelationSelection`, `OAI.CircleDomainRigidity.ConstrainedCostCode`, `OAI.CircleDomainRigidity.EndpointCode`, `OAI.CircleDomainRigidity.FiniteCostCode`, `OAI.CircleDomainRigidity.FiniteJordanModelUniformization`, `OAI.CircleDomainRigidity.instMeasurableSpaceTagSlot` and `OAI.CircleDomainRigidity.pathCostMeasure` (definitions bundle `Q146C004` of this split); `OAI.CircleDomainRigidity.PlanarSobolevCoarea`, `OAI.CircleDomainRigidity.PrincipalRealBeltrami`, `OAI.CircleDomainRigidity.UnitDiskCrosscutSeparation`, `OAI.CircleDomainRigidity.UnorientedFiniteCircleGreenFormula`, `OAI.CircleDomainRigidity.instBorelSpaceSphere_75` and `OAI.CircleDomainRigidity.MatchedConformalEnds.realPlaneDomain` (definitions bundle `Q146C005` of this split); `OAI.CircleDomainRigidity.MatchedConformalEnds`, `OAI.CircleDomainRigidity.MatchedConformalEnds.IndexedMatchedPair` and `OAI.CircleDomainRigidity.MatchedConformalEnds.MatchedRoundDisks` (definitions bundle `Q146C007` of this split); `OAI.CircleDomainRigidity.PrincipalConductivityScalarSolver` and `OAI.CircleDomainRigidity.SmoothCompactMetricSphereUniformization` (definitions bundle `Q146C008` of this split); `OAI.CircleDomainRigidity.SmoothRegularJordanCollars`, `OAI.CircleDomainRigidity.MatchedConformalEnds.MatchedRealMask`, `OAI.CircleDomainRigidity.MatchedConformalEnds.realMaskValue` and `OAI.CircleDomainRigidity.MatchedConformalEnds.realSelectedScalar` (definitions bundle `Q146C010` of this split); `OAI.CircleDomainRigidity.IsConformalEquivalence` and `OAI.CircleDomainRigidity.Sphere` (the published bundle `Def_KoebeCircleDomains`).
--
--   **Used by.** The proof of `OAI.CircleDomainRigidity.circleDomainRemovabilityRigidity_of_scalar_solver` of this split imports it.
-- source:
--   OpenAI, Koebe's circle-domain conjecture and rigidity (result family 71), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 71; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/Koebes-Circle-Domain-Conjecture-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Analysis/CircleDomains/Rigidity/MatchedMaskGlobalSobolev.lean (declaration OAI.CircleDomainRigidity.MatchedConformalEnds.MatchedRealMask.global_sobolev_of_published_inputs)

import Mathlib
import Definitions.Def_KoebeCircleDomains
import Definitions.Def_Q146C010

section

attribute [-instance] _root_.OAI.CannonEmbeddedArc.Arc.graphVertices_finite _root_.OAI.CannonMobius.sphereMetric _root_.OAI.CannonPlanar.instLocallyPathConnectedSpaceElemRealUnitInterval_solutions
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

open Set Function Filter MeasureTheory Metric
open scoped Topology ENNReal NNReal
noncomputable section
namespace CircleDomainRigidity
open FiniteTransfer
attribute [local instance] sphereMetric sphereBorel
variable [MeasurableSpace C(PathTime, Sphere)] [BorelSpace C(PathTime, Sphere)]
namespace MatchedConformalEnds
variable {G : Set Sphere} {f : Sphere → Sphere} {D : MatchedConformalEnds G f}
variable [Encodable D.IndexedMatchedPair]

 local instance localInst_r60ce71_1 : BorelSpace Sphere := ⟨rfl⟩
theorem MatchedRealMask.global_sobolev_of_published_inputs
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
    {E : D.MatchedRoundDisks} {hG : IsOpen G} {hf : IsConformalEquivalence f G (f '' G)}
    {φ : Sphere → ℝ} {L : ℝ≥0} {m : ℕ} (M : MatchedRealMask E hG hf φ L m)
    (hinf : OnePoint.infty ∈ G)
    (hb : ContDiffOn ℝ 1 (D.realSelectedScalar hG hf φ) (realPlaneDomain G))
    (hb2 : MemLp (fderiv ℝ (D.realSelectedScalar hG hf φ)) 2 (volume.restrict (realPlaneDomain G))) :
    Nonempty (DeGiorgi.MemW1pWitness 2
      (D.realMaskValue E hG hf φ L M.cutoff ∘ euclideanPlaneCoordinates) univ) := by
  sorry

end MatchedConformalEnds
end CircleDomainRigidity

end

end OAI
end
