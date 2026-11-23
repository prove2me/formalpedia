-- Prove2me | Theorems.Thm_GlobalTheory_Ex_TateInh_isoRefl_rel
-- name    : GlobalTheory.Ex.TateInh.isoRefl_rel
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T12:45:58.585392+00:00
-- url     : https://prove2.me/theorems/486ea224-f6df-4a86-a652-34b6466d77ac
-- title:
--   Tate Inh: iso Refl rel
-- statement:
--   The Tate Inh construction uses the iso Refl rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/NotAllMatchRankZero.lean#L484-L486
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/Degenerations/NotAllMatchRankZero.lean#L484-L486

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_SepticCharacterInjective
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_NotAllMatchRankZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.Ex
variable {O : Type} [CommRing O]
open GlobalTheory.Ex.TateInh

theorem GlobalTheory.Ex.TateInh.isoRefl_rel (N : NumD O) (g g' : N.Gt) : (isoRefl N).Rel g g' ↔ g' = g := by sorry
