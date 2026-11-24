-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_DetScale_smul_map_pi
-- name    : GlobalTheory.CompanionTheory.SW.DetScale.smul_map_pi
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:03:41.315662+00:00
-- url     : https://prove2.me/theorems/75471943-f6b4-4896-8370-fc075b554547
-- title:
--   Det Scale: smul map pi
-- statement:
--   The Det Scale construction uses the smul map pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HaarMapLinearScalingByDeterminant.lean#L74-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/HaarMapLinearScalingByDeterminant.lean#L74-L126

import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HaarMapLinearScalingByDeterminant
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.DetScale
open Matrix
open scoped Pointwise

theorem GlobalTheory.CompanionTheory.SW.DetScale.smul_map_pi {F : Type} [Field F] {R : Type} [CommRing R] [Algebra F R]
    [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R]
    [SecondCountableTopology R] [T2Space R] [MeasurableSpace R] [BorelSpace R]
    {ι : Type} [Fintype ι] [DecidableEq ι] (lam : Measure R) [lam.IsAddHaarMeasure]
    (A : Matrix ι ι F) (h : A.det ≠ 0) :
    distribHaarChar R (Units.map (algebraMap F R : F →* R) (Units.mk0 A.det h)) •
        (Measure.pi fun _ : ι => lam).map (fun x => A.map (algebraMap F R) *ᵥ x) =
      Measure.pi fun _ : ι => lam := by sorry
