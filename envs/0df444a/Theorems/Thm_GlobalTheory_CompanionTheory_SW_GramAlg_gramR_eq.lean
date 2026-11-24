-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_GramAlg_gramR_eq
-- name    : GlobalTheory.CompanionTheory.SW.GramAlg.gramR_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T12:05:13.739133+00:00
-- url     : https://prove2.me/theorems/92811749-6ad2-441d-b2a9-0a83959560c5
-- title:
--   Gram Alg: gram R eq
-- statement:
--   The Gram Alg construction uses the gram R eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramRightActionIdentities.lean#L61-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/GramRightActionIdentities.lean#L61-L65

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_GramRightActionIdentities
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.GramAlg
variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable (R : Type) [CommRing R] [Algebra F R]
variable {M n : ℕ}

theorem GlobalTheory.CompanionTheory.SW.GramAlg.gramR_eq (σ : E →ₐ[F] E) (J : Matrix (Fin M) (Fin M) E) (X : Fin n → Fin M → R ⊗[F] E) :
    gramR R σ J X =
      (cT (sigR R σ) (colM X) * JR R J : Matrix (Fin n) (Fin M) (R ⊗[F] E)) * colM X := by sorry
