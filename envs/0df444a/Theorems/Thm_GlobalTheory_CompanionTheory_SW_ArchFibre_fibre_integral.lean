-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_ArchFibre_fibre_integral
-- name    : GlobalTheory.CompanionTheory.SW.ArchFibre.fibre_integral
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T12:01:32.528745+00:00
-- url     : https://prove2.me/theorems/4ef2bde2-2e77-4a2c-9863-92bbc8978905
-- title:
--   Arch Fibre: fibre integral
-- statement:
--   The Arch Fibre construction uses the fibre integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ArchimedeanBinaryGramDensity.lean#L152-L268
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ArchimedeanBinaryGramDensity.lean#L152-L268

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_BinaryMassMeans_MeanVal
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyReal
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_CoordinateHaarMeasure
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitsOpenEmbeddingLocalTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorel
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ArchimedeanBinaryGramDensity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.Rg.Mass
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter
open scoped TensorProduct ENNReal NNReal
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.ArchFibre
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}

theorem GlobalTheory.CompanionTheory.SW.ArchFibre.fibre_integral (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R]
    [BorelSpace R] (hloc : IsLocR R) (h : IsCMExt F E σ) (hJ : IsHermND σ J)
    {d : ℕ} (b : Module.Basis (Fin d) F E) (lam : Measure R) (hlam : lam.IsAddHaarMeasure)
    (m : HermR R σ 1 → Measure (Fin 1 → Fin M → R ⊗[F] E))
    (hfib : IsGramFib R σ J 1 (coordW R b lam 1 M) (coordHerm R σ b lam 1) m)
    (φ : (Fin 1 → Fin M → R ⊗[F] E) → ℝ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφ0 : ∀ X, 0 ≤ φ X) (hφU : tsupport φ ⊆ {X | IsUnit (gramR R σ J X).det}) :
    Continuous (fun s : R => ∫ X, φ X ∂(m (hermScal R σ s))) ∧
    HasCompactSupport (fun s : R => ∫ X, φ X ∂(m (hermScal R σ s))) ∧
    (∀ s : R, ∫⁻ X, ENNReal.ofReal (φ X) ∂(m (hermScal R σ s)) =
      ENNReal.ofReal (∫ X, φ X ∂(m (hermScal R σ s)))) ∧
    ENNReal.ofReal (∫ s, (∫ X, φ X ∂(m (hermScal R σ s))) ∂lam) =
      ∫⁻ X, ENNReal.ofReal (φ X) ∂(coordW R b lam 1 M) := by sorry
