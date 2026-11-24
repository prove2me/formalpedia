-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_LocGauss_fibre_lintegral_eq_density
-- name    : GlobalTheory.CompanionTheory.SW.LocGauss.fibre_lintegral_eq_density
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T12:07:24.462325+00:00
-- url     : https://prove2.me/theorems/c5626e52-8e7f-42e4-ade6-44a545f8d393
-- title:
--   Loc Gauss: fibre lintegral eq density
-- statement:
--   The Loc Gauss construction uses the fibre lintegral eq density property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ArchimedeanGramFiberContinuousDensity.lean#L19-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/ArchimedeanGramFiberContinuousDensity.lean#L19-L129

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ContinuousDensitiesEqOfIntegralsOnCompacts
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_DisintegrationDensityUnique
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramRightActionIdentities
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorel
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ExistsSizeMulLe
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyRealStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitsOpenEmbeddingLocalTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramFiberMeasuresIntegralFormulaStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianLocalContinuousCongruenceSectionStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_SizeFunctionRapidDecayIntegrableStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_ArchimedeanGramFiberContinuousDensity
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LocGauss

theorem GlobalTheory.CompanionTheory.SW.LocGauss.fibre_lintegral_eq_density {V X Y : Type}
    [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V]
    [MeasurableSpace V] [BorelSpace V]
    [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X]
    [MeasurableSpace X] [BorelSpace X]
    (μ : Measure V) (ν : Measure X) [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure]
    (f : V → Y) (g : V → X) (ι : X → Y) (hι : Function.Injective ι) (hg : Continuous g)
    (hf : ∀ v, f v = ι (g v)) (B : Set X) (fib : X → Measure V)
    (hfib : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' B) ν B fib)
    (b₀ : X) (O : Set X) (hO : IsOpen O) (hOB : O ⊆ B) (hb₀ : b₀ ∈ O)
    (T : X → V → V) (κ : X → ℝ≥0)
    (hT : ContinuousOn (fun p : X × V => T p.1 p.2) (O ×ˢ Set.univ))
    (hκ : ContinuousOn κ O) (hκ0 : ∀ b ∈ O, κ b ≠ 0)
    (hm : ∀ b ∈ O, fib b = (κ b : ℝ≥0∞) • (fib b₀).map (T b))
    (w u : V → ℝ≥0∞) (hw : Measurable w) (hu : Continuous u) (hwμ : ∫⁻ v, w v ∂μ < ∞)
    (C : ℝ≥0) (huw : ∀ v, u v ≤ C * w v)
    (hwT : ∀ L : Set X, IsCompact L → L ⊆ O → ∃ c : ℝ≥0, ∀ b ∈ L, ∀ v,
      w (T b v) ≤ c * w v ∧ w v ≤ c * w (T b v))
    (d : X → ℝ≥0∞) (hd : ContinuousOn d O)
    (hdens : ∀ L : Set X, IsCompact L → L ⊆ O → ∫⁻ v in g ⁻¹' L, u v ∂μ = ∫⁻ b in L, d b ∂ν) :
    ∫⁻ v, u v ∂(fib b₀) = d b₀ := by sorry
