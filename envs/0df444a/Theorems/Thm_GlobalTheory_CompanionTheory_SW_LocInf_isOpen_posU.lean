-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_LocInf_isOpen_posU
-- name    : GlobalTheory.CompanionTheory.SW.LocInf.isOpen_posU
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:29:21.074986+00:00
-- url     : https://prove2.me/theorems/344dd0a3-0d56-4786-bb5e-6d06f8e4d895
-- title:
--   Loc Inf: is Open pos U
-- statement:
--   The Loc Inf construction uses the is Open pos U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/InfiniteAdelesLocalRingTotallyReal.lean#L29-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/InfiniteAdelesLocalRingTotallyReal.lean#L29-L30

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

theorem GlobalTheory.CompanionTheory.SW.LocInf.isOpen_posU (ι : Type) [Fintype ι] : IsOpen (posU ι : Set (ι → ℝ)ˣ) := by sorry
