-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_TargetUnip_det_eq_one_of_level
-- name    : GlobalTheory.RootEx.TargetUnip.det_eq_one_of_level
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T19:30:02.761971+00:00
-- url     : https://prove2.me/theorems/0acc8704-6a7d-4dbe-95ab-be998529421e
-- title:
--   Target Unip: det eq one of level
-- statement:
--   The Target Unip construction uses the det eq one of level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/OpEOmTargetUnipotent.lean#L11-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/OpEOmTargetUnipotent.lean#L11-L24

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_LinearChangeOfVariablesLocalFieldMatrix
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_OpEOmTargetUnipotent
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.TargetUnip

theorem GlobalTheory.RootEx.TargetUnip.det_eq_one_of_level {k ι : Type*} [Field k] [Fintype ι] [DecidableEq ι] (f : ι → ℕ)
    (M : Matrix ι ι k) (hM : ∀ r s, f s ≤ f r → M r s = (1 : Matrix ι ι k) r s) : M.det = 1 := by sorry
