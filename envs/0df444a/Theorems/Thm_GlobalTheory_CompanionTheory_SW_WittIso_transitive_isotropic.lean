-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_WittIso_transitive_isotropic
-- name    : GlobalTheory.CompanionTheory.SW.WittIso.transitive_isotropic
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:12:39.688468+00:00
-- url     : https://prove2.me/theorems/7dbd0e00-8f77-44f1-b71e-81253f00bd0a
-- title:
--   Witt Iso: transitive isotropic
-- statement:
--   The Witt Iso construction uses the transitive isotropic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/UnitaryTransitiveOnIsotropicVectors.lean#L86-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/UnitaryTransitiveOnIsotropicVectors.lean#L86-L105

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

theorem GlobalTheory.CompanionTheory.SW.WittIso.transitive_isotropic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E),
    IsHermND σ J → ∀ x y : Fin M → E, x ≠ 0 → y ≠ 0 → hE σ J x x = 0 → hE σ J y y = 0 →
    ∃ g ∈ UJ (σ : E →+* E) J, (g : Matrix (Fin M) (Fin M) E) *ᵥ x = y := by sorry
