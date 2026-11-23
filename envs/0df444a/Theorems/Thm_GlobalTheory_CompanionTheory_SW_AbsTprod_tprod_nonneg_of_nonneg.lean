-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_AbsTprod_tprod_nonneg_of_nonneg
-- name    : GlobalTheory.CompanionTheory.SW.AbsTprod.tprod_nonneg_of_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:23:38.30182+00:00
-- url     : https://prove2.me/theorems/5856e23d-c03f-44f6-bf12-b9aa18835df5
-- title:
--   Abs Tprod: tprod nonneg of nonneg
-- statement:
--   The Abs Tprod construction uses the tprod nonneg of nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/InfiniteProductMultipliable.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/InfiniteProductMultipliable.lean#L15-L17

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteProductMultipliable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.AbsTprod

theorem GlobalTheory.CompanionTheory.SW.AbsTprod.tprod_nonneg_of_nonneg {ι : Type} {a : ι → ℝ} (hm : Multipliable a)
    (h0 : ∀ v, 0 ≤ a v) : 0 ≤ ∏' v, a v := by sorry
