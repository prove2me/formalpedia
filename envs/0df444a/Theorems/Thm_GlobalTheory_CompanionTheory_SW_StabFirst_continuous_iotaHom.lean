-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_StabFirst_continuous_iotaHom
-- name    : GlobalTheory.CompanionTheory.SW.StabFirst.continuous_iotaHom
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T12:09:13.055319+00:00
-- url     : https://prove2.me/theorems/a8d15b2e-f5f7-42be-a9fa-92ce4b5723f4
-- title:
--   Stab First: continuous iota Hom
-- statement:
--   The Stab First construction uses the continuous iota Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneRightInjective.lean#L292-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneRightInjective.lean#L292-L301

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_BlockOneRightInjective
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.StabFirst
variable {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R]
  (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (s : E)
variable [TopologicalSpace R]

theorem GlobalTheory.CompanionTheory.SW.StabFirst.continuous_iotaHom : Continuous (iotaHom R σ J s) := by sorry
