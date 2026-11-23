-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_AbsTprod_multipliable_of_summable_abs_sub_one
-- name    : GlobalTheory.CompanionTheory.SW.AbsTprod.multipliable_of_summable_abs_sub_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:23:36.236797+00:00
-- url     : https://prove2.me/theorems/6395c176-ca2c-4444-a05b-86ce05dcda8f
-- title:
--   Abs Tprod: multipliable of summable abs sub one
-- statement:
--   The Abs Tprod construction uses the multipliable of summable abs sub one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/InfiniteProductMultipliable.lean#L8-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/InfiniteProductMultipliable.lean#L8-L13

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

theorem GlobalTheory.CompanionTheory.SW.AbsTprod.multipliable_of_summable_abs_sub_one {ι : Type} {a : ι → ℝ}
    (h : Summable (fun v => |a v - 1|)) : Multipliable a := by sorry
