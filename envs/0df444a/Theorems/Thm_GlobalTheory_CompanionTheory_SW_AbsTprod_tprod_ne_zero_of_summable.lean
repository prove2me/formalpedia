-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_AbsTprod_tprod_ne_zero_of_summable
-- name    : GlobalTheory.CompanionTheory.SW.AbsTprod.tprod_ne_zero_of_summable
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T12:01:13.690508+00:00
-- url     : https://prove2.me/theorems/c260713d-5068-4866-b770-bf7b2d6c24fe
-- title:
--   Abs Tprod: tprod ne zero of summable
-- statement:
--   The Abs Tprod construction uses the tprod ne zero of summable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/InfiniteProductMultipliable.lean#L19-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/InfiniteProductMultipliable.lean#L19-L24

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

theorem GlobalTheory.CompanionTheory.SW.AbsTprod.tprod_ne_zero_of_summable {ι : Type} {a : ι → ℝ}
    (h : Summable (fun v => |a v - 1|)) (h0 : ∀ v, a v ≠ 0) : ∏' v, a v ≠ 0 := by sorry
