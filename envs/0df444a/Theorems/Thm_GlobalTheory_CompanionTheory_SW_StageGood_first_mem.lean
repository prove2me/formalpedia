-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_StageGood_first_mem
-- name    : GlobalTheory.CompanionTheory.SW.StageGood.first_mem
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:23:11.7208+00:00
-- url     : https://prove2.me/theorems/64530f3d-a75d-4147-a7da-93a0eea68cca
-- title:
--   Stage Good: first mem
-- statement:
--   The Stage Good construction uses the first mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LocalMeasuresOrthogonalSumAlmostAllPlaces.lean#L33-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LocalMeasuresOrthogonalSumAlmostAllPlaces.lean#L33-L40

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneDetHermitianGram
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneRightInjective
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeStableAlmostEverywhere
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CompletionIsLocalRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LatticeGramScalarAlmostAll
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresInvariantStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicTupleProjectionsStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_AdelicUnitaryGroupLocallyCompactStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalMeasuresOrthogonalSumAlmostAllPlaces
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.StageGood

theorem GlobalTheory.CompanionTheory.SW.StageGood.first_mem {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d M n : ℕ}
    (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E)
    (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (h : HA (Fv F v) σ J)
    (X : Fin n → Fin M → Fv F v ⊗[F] E)
    (hX : actW (Fv F v) σ J h (consTup X) ∈ latV b v) :
    actW (Fv F v) σ J h (fun _ : Fin 1 => Fin.cons 1 (fun _ => 0)) ∈ latV b v := by sorry
