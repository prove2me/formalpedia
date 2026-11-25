-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_LocInv_iUnion_valBall_sub
-- name    : GlobalTheory.CompanionTheory.SW.LocInv.iUnion_valBall_sub
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:05:15.999091+00:00
-- url     : https://prove2.me/theorems/d3aa6a5b-f022-473f-b5aa-95b16e6c8b3f
-- title:
--   Loc Inv: i Union val Ball sub
-- statement:
--   The Loc Inv construction uses the i Union val Ball sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LocalFieldSelfdualMeasureExists.lean#L139-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/LocalFieldSelfdualMeasureExists.lean#L139-L143

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_CountingDefinitions_AdelicEulerProducts_IsEulerProd
import Definitions.Def_GroundTheory_LocalFields_LocalFourier
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_LocalFieldSelfdualMeasureExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.LocInv
open GroundTheory.LocalField ValuativeRel MeasureTheory Topology Filter
open scoped NNReal ENNReal
variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [MeasurableSpace K] [BorelSpace K]

theorem GlobalTheory.CompanionTheory.SW.LocInv.iUnion_valBall_sub (n : ℤ) : ⋃ k : ℕ, (valBall K (n - (k : ℤ)) : Set K) = Set.univ := by sorry
