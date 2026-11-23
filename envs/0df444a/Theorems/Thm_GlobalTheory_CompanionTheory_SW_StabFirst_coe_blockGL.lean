-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_StabFirst_coe_blockGL
-- name    : GlobalTheory.CompanionTheory.SW.StabFirst.coe_blockGL
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:51:44.272108+00:00
-- url     : https://prove2.me/theorems/473e1cb2-6631-49db-8c95-eec5e2d04d84
-- title:
--   Stab First: coe block GL
-- statement:
--   The Stab First construction uses the coe block GL property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneRightInjective.lean#L57-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/BlockOneRightInjective.lean#L57-L59

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
variable {K : Type} [CommRing K] {M : ℕ}

theorem GlobalTheory.CompanionTheory.SW.StabFirst.coe_blockGL (g : GL (Fin M) K) :
    ((blockGL g : GL (Fin (M + 1)) K) : Matrix (Fin (M + 1)) (Fin (M + 1)) K) =
      blockOne 1 (g : Matrix (Fin M) (Fin M) K) := by sorry
