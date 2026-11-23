-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_LocInf_isOpen_pos
-- name    : GlobalTheory.CompanionTheory.SW.LocInf.isOpen_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:30:15.686717+00:00
-- url     : https://prove2.me/theorems/66bc13ba-59c5-4a0e-b524-024b3bd74b5b
-- title:
--   Loc Inf: is Open pos
-- statement:
--   The Loc Inf construction uses the is Open pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/InfiniteAdelesLocalRingTotallyReal.lean#L22-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/InfiniteAdelesLocalRingTotallyReal.lean#L22-L27

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteAdelesLocalRingTotallyReal
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
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LocInf

theorem GlobalTheory.CompanionTheory.SW.LocInf.isOpen_pos (ι : Type) [Finite ι] : IsOpen {x : ι → ℝ | ∀ i, 0 < x i} := by sorry
