-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_KAlg_tmul_one_injective
-- name    : GlobalTheory.CompanionTheory.SW.KAlg.tmul_one_injective
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:06:54.012883+00:00
-- url     : https://prove2.me/theorems/fb5f012b-29b9-43aa-9be6-2e441abc7139
-- title:
--   KAlg: tmul one injective
-- statement:
--   The KAlg construction uses the tmul one injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TensorInvolutionAlgebraProperties.lean#L67-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TensorInvolutionAlgebraProperties.lean#L67-L72

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
variable {R : Type} [CommRing R] [Algebra F R]

theorem GlobalTheory.CompanionTheory.SW.KAlg.tmul_one_injective (b : Module.Basis (Fin 2) F E) {δ : E} (hb0 : b 0 = 1) (hb1 : b 1 = δ) :
    Function.Injective (Algebra.TensorProduct.includeLeft : R →ₐ[F] R ⊗[F] E) := by sorry
