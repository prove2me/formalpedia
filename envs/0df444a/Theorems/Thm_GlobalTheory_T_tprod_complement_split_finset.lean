-- Prove2me | Theorems.Thm_GlobalTheory_T_tprod_complement_split_finset
-- name    : GlobalTheory.T.tprod_complement_split_finset
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:39:55.587142+00:00
-- url     : https://prove2.me/theorems/30101f09-16d1-552f-bf20-52c877cdae28
-- title:
--   T: tprod complement split finset
-- statement:
--   The T construction uses the tprod complement split finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TprodComplementSplitFinsetStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/AdelicAnalysis/TprodComplementSplitFinsetStatement.lean#L7-L8

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TprodComplementSplitFinset
import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_AdelicAnalysis_TprodComplementSplitFinsetStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.tprod_complement_split_finset : ∀ (ι : Type) [DecidableEq ι] (a : ι → ℝ) (S S' : Finset ι), Summable (fun v => |a v - 1|) → S ⊆ S' → ∏' v : {v // v ∉ S}, a v.1 = (∏ v ∈ S' \ S, a v) * ∏' v : {v // v ∉ S'}, a v.1 := by sorry
