-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_StabFirst_isClosed_range_iotaHom
-- name    : GlobalTheory.CompanionTheory.SW.StabFirst.isClosed_range_iotaHom
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:09:04.988948+00:00
-- url     : https://prove2.me/theorems/7928de50-8926-4801-a2f7-a2b41e661357
-- title:
--   Stab First: is Closed range iota Hom
-- statement:
--   The Stab First construction uses the is Closed range iota Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneRightInjective.lean#L321-L334
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneRightInjective.lean#L321-L334

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

theorem GlobalTheory.CompanionTheory.SW.StabFirst.isClosed_range_iotaHom [T2Space (R ⊗[F] E)] (hs : s ≠ 0) :
    IsClosed (Set.range (iotaHom R σ J s)) := by sorry
