-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_StabFirst_mat_iotaHom
-- name    : GlobalTheory.CompanionTheory.SW.StabFirst.mat_iotaHom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:30:32.751484+00:00
-- url     : https://prove2.me/theorems/67e4d7d8-4a4c-4020-bcf8-b811d402b1db
-- title:
--   Stab First: mat iota Hom
-- statement:
--   The Stab First construction uses the mat iota Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneRightInjective.lean#L196-L197
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneRightInjective.lean#L196-L197

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

theorem GlobalTheory.CompanionTheory.SW.StabFirst.mat_iotaHom (u : HA R σ J) :
    HA.mat R σ _ (iotaHom R σ J s u) = blockGL (HA.mat R σ J u) := by sorry
