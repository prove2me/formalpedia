-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_StabFirst_isEmbedding_pairMap
-- name    : GlobalTheory.CompanionTheory.SW.StabFirst.isEmbedding_pairMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:51:21.801846+00:00
-- url     : https://prove2.me/theorems/97251a95-ea70-45dc-9ebc-c6196e1a7fce
-- title:
--   Stab First: is Embedding pair Map
-- statement:
--   The Stab First construction uses the is Embedding pair Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneRightInjective.lean#L287-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneRightInjective.lean#L287-L290

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

theorem GlobalTheory.CompanionTheory.SW.StabFirst.isEmbedding_pairMap {N : ℕ} (J' : Matrix (Fin N) (Fin N) E) :
    IsEmbedding (pairMap R σ J') := by sorry
