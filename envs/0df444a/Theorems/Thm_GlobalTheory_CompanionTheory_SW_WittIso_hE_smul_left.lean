-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_WittIso_hE_smul_left
-- name    : GlobalTheory.CompanionTheory.SW.WittIso.hE_smul_left
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:12:45.39961+00:00
-- url     : https://prove2.me/theorems/c5ce80e7-7d8e-4865-a160-a6715fe3b29c
-- title:
--   Witt Iso: h E smul left
-- statement:
--   The Witt Iso construction uses the h E smul left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/UnitaryTransitiveOnIsotropicVectors.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/UnitaryTransitiveOnIsotropicVectors.lean#L30-L32

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

theorem GlobalTheory.CompanionTheory.SW.WittIso.hE_smul_left (c : E) (x y : Fin M → E) : hE σ J (c • x) y = σ c * hE σ J x y := by sorry
