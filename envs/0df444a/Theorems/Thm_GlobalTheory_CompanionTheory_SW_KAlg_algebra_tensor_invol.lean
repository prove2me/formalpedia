-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_KAlg_algebra_tensor_invol
-- name    : GlobalTheory.CompanionTheory.SW.KAlg.algebra_tensor_invol
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:36:40.219036+00:00
-- url     : https://prove2.me/theorems/df2575f3-da4f-43eb-bc93-b4ea41e7282f
-- title:
--   KAlg: algebra tensor invol
-- statement:
--   The KAlg construction uses the algebra tensor invol property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TensorInvolutionAlgebraProperties.lean#L76-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TensorInvolutionAlgebraProperties.lean#L76-L156

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TensorInvolutionAlgebraProperties
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.KAlg

theorem GlobalTheory.CompanionTheory.SW.KAlg.algebra_tensor_invol : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (R : Type) [CommRing R] [Algebra F R] [IsArtinianRing R] [IsReduced R],
    IsArtinianRing (R ⊗[F] E) ∧ IsReduced (R ⊗[F] E) ∧ IsUnit (2 : R ⊗[F] E) ∧
      (∀ y, sigR R σ (sigR R σ y) = y) ∧ (∃ δ : R ⊗[F] E, IsUnit δ ∧ sigR R σ δ = -δ) ∧
      (∀ y : R ⊗[F] E, sigR R σ y = y → ∃ r : R, y = r ⊗ₜ[F] (1 : E)) ∧
      ∀ r : R, IsUnit (r ⊗ₜ[F] (1 : E) : R ⊗[F] E) ↔ IsUnit r := by sorry
