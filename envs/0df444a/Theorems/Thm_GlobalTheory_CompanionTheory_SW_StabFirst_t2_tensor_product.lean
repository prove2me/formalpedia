-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_StabFirst_t2_tensor_product
-- name    : GlobalTheory.CompanionTheory.SW.StabFirst.t2_tensor_product
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T12:10:44.265057+00:00
-- url     : https://prove2.me/theorems/71dc1ba5-4f13-4670-9ccf-0ffee5a2a268
-- title:
--   Stab First: t2 tensor product
-- statement:
--   The Stab First construction uses the t2 tensor product property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneRightInjective.lean#L340-L347
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneRightInjective.lean#L340-L347

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

theorem GlobalTheory.CompanionTheory.SW.StabFirst.t2_tensor_product {F E : Type} [Field F] [Field E] [Algebra F E] [Module.Finite F E] (R : Type)
    [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] :
    T2Space (R ⊗[F] E) := by sorry
