-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SW_TailConst_tail_eq_mul_tail_insert
-- name    : GlobalTheory.CompanionTheory.SW.TailConst.tail_eq_mul_tail_insert
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:10:10.549419+00:00
-- url     : https://prove2.me/theorems/80e87117-fc3a-4c6b-8545-3039c428cc80
-- title:
--   Tail Const: tail eq mul tail insert
-- statement:
--   The Tail Const construction uses the tail eq mul tail insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/InfiniteProductRenormalization.lean#L8-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/InfiniteProductRenormalization.lean#L8-L32

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

theorem GlobalTheory.CompanionTheory.SW.TailConst.tail_eq_mul_tail_insert {ι : Type} [DecidableEq ι] (a : ι → ℝ)
    (hs : Summable (fun v => |a v - 1|)) (S : Finset ι) (v : ι) (hv : v ∉ S) :
    ∏' w : {w // w ∉ S}, a w.1 = a v * ∏' w : {w // w ∉ insert v S}, a w.1 := by sorry
