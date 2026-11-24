-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_KAlg_exists_basis_one_delta
-- name    : GlobalTheory.CompanionTheory.SW.KAlg.exists_basis_one_delta
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:06:11.467614+00:00
-- url     : https://prove2.me/theorems/c5562fe7-d54b-4875-a64a-35675ee8e3d5
-- title:
--   KAlg: exists basis one delta
-- statement:
--   The KAlg construction uses the exists basis one delta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TensorInvolutionAlgebraProperties.lean#L13-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TensorInvolutionAlgebraProperties.lean#L13-L36

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
variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem GlobalTheory.CompanionTheory.SW.KAlg.exists_basis_one_delta (σ : E →ₐ[F] E) {δ : E} (hδ : σ δ = -δ) (h0 : δ ≠ 0)
    (hfr : Module.finrank F E = 2) (h2 : (2 : F) ≠ 0) :
    ∃ b : Module.Basis (Fin 2) F E, b 0 = 1 ∧ b 1 = δ := by sorry
