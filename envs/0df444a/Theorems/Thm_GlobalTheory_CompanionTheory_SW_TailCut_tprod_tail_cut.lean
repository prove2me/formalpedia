-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_TailCut_tprod_tail_cut
-- name    : GlobalTheory.CompanionTheory.SW.TailCut.tprod_tail_cut
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:11:47.542926+00:00
-- url     : https://prove2.me/theorems/eb131036-84e4-45fb-b0ed-6be2cea45e07
-- title:
--   Tail Cut: tprod tail cut
-- statement:
--   The Tail Cut construction uses the tprod tail cut property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TprodComplementSplitFinset.lean#L9-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TprodComplementSplitFinset.lean#L9-L40

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteProductMultipliable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TprodComplementSplitFinset
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.TailCut

theorem GlobalTheory.CompanionTheory.SW.TailCut.tprod_tail_cut : ∀ (ι : Type) [DecidableEq ι] (a : ι → ℝ) (S S' : Finset ι),
    Summable (fun v => |a v - 1|) → S ⊆ S' →
      ∏' v : {v // v ∉ S}, a v.1 = (∏ v ∈ S' \ S, a v) * ∏' v : {v // v ∉ S'}, a v.1 := by sorry
