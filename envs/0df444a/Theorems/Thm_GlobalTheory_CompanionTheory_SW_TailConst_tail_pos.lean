-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_TailConst_tail_pos
-- name    : GlobalTheory.CompanionTheory.SW.TailConst.tail_pos
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:11:59.199355+00:00
-- url     : https://prove2.me/theorems/108a30b5-fded-4b24-9a01-cfd2dca35d25
-- title:
--   Tail Const: tail pos
-- statement:
--   The Tail Const construction uses the tail pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/InfiniteProductRenormalization.lean#L34-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/InfiniteProductRenormalization.lean#L34-L37

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteProductMultipliableStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_InfiniteProductRenormalization
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.TailConst

theorem GlobalTheory.CompanionTheory.SW.TailConst.tail_pos {ι : Type} (a : ι → ℝ) (hs : Summable (fun v => |a v - 1|)) (S : Finset ι)
    (hpos : ∀ v, v ∉ S → 0 < a v) : 0 < ∏' w : {w // w ∉ S}, a w.1 := by sorry
