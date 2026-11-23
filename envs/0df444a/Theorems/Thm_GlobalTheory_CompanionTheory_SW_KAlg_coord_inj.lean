-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_KAlg_coord_inj
-- name    : GlobalTheory.CompanionTheory.SW.KAlg.coord_inj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:29:03.052595+00:00
-- url     : https://prove2.me/theorems/4c1dd432-5589-453f-8554-1708d70aa57b
-- title:
--   KAlg: coord inj
-- statement:
--   The KAlg construction uses the coord inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TensorInvolutionAlgebraProperties.lean#L51-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TensorInvolutionAlgebraProperties.lean#L51-L65

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

theorem GlobalTheory.CompanionTheory.SW.KAlg.coord_inj (b : Module.Basis (Fin 2) F E) {δ : E} (hb0 : b 0 = 1) (hb1 : b 1 = δ)
    {a c a' c' : R} (h : a ⊗ₜ[F] (1 : E) + c ⊗ₜ[F] δ = a' ⊗ₜ[F] (1 : E) + c' ⊗ₜ[F] δ) :
    a = a' ∧ c = c' := by sorry
