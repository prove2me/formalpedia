-- Prove2me | Theorems.Thm_GlobalTheory_Models_one_le_w_and_wst
-- name    : GlobalTheory.Models.one_le_w_and_wst
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T03:11:32.317298+00:00
-- url     : https://prove2.me/theorems/bc4a10b5-521d-400a-ad44-349779e658d3
-- title:
--   Models: one le w and wst
-- statement:
--   The Models construction uses the one le w and wst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/TwistedModelAdmissibleCocycles.lean#L241-L244
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/TwistedModelAdmissibleCocycles.lean#L241-L244

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_PowerSeriesOneAddConstMulXMulInv
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MkMemAdmissibleAtIffCocycle
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwistedModelAdmissibleCocycles
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.Models
open scoped LaurentSeries PowerSeries
open GlobalTheory.PhiGam GlobalTheory.AdmLoc
open ReciprocityTheory.Def (Z1)
variable {k G : Type} [Field k] [Group G]
variable {l n : ℕ} {R : RingPG k l}

theorem GlobalTheory.Models.one_le_w_and_wst {r : ℕ} (Dt : TopData n r) (i : ZMod n) : 1 ≤ Dt.w i ∧ 1 ≤ Dt.wst i := by sorry
