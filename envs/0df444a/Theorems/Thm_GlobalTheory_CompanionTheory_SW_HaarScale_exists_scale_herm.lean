-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_HaarScale_exists_scale_herm
-- name    : GlobalTheory.CompanionTheory.SW.HaarScale.exists_scale_herm
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:02:10.558361+00:00
-- url     : https://prove2.me/theorems/a176a226-b8e2-467c-89b1-5a90ea83badc
-- title:
--   Haar Scale: exists scale herm
-- statement:
--   The Haar Scale construction uses the exists scale herm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsContinuousScale.lean#L223-L278
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsContinuousScale.lean#L223-L278

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRing
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitsOpenEmbeddingLocalTensor
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_HermitianMatricesLocallyCompactBorel
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorLocallyCompactRingStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitsOpenEmbeddingLocalTensorStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsContinuousScale
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.HaarScale
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem GlobalTheory.CompanionTheory.SW.HaarScale.exists_scale_herm (σ : E →ₐ[F] E) (hσ : IsCMExt F E σ) (R : Type) [CommRing R] [Algebra F R]
    [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (hR : IsLocR R) (n : ℕ)
    (ν : Measure (HermR R σ n)) (hν : ν.IsAddHaarMeasure) :
    ∃ B : Matrix (Fin n) (Fin n) (R ⊗[F] E) → ℝ≥0, ContinuousOn B {g | IsUnit g.det} ∧
      ∀ g, IsUnit g.det → ∀ τ : HermR R σ n → HermR R σ n,
        (∀ S, (τ S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) =
          conjT R σ g * (S : Matrix (Fin n) (Fin n) (R ⊗[F] E)) * g) → ν.map τ = B g • ν := by sorry
