-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_WittIso_exists_hE_ne_zero
-- name    : GlobalTheory.CompanionTheory.SW.WittIso.exists_hE_ne_zero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T12:12:58.086536+00:00
-- url     : https://prove2.me/theorems/13fe38d0-0018-4fff-a98b-843bf4cfdac6
-- title:
--   Witt Iso: exists h E ne zero
-- statement:
--   The Witt Iso construction uses the exists h E ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/UnitaryTransitiveOnIsotropicVectors.lean#L44-L58
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/UnitaryTransitiveOnIsotropicVectors.lean#L44-L58

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_HypJ
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_WittExtensionGlobalStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_UnitaryTransitiveOnIsotropicVectors
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.WittIso
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
variable {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) {M : ℕ}
  (J : Matrix (Fin M) (Fin M) E)
variable {σ J}

theorem GlobalTheory.CompanionTheory.SW.WittIso.exists_hE_ne_zero (hdet : J.det ≠ 0) {x : Fin M → E} (hx : x ≠ 0) :
    ∃ w, hE σ J x w ≠ 0 := by sorry
