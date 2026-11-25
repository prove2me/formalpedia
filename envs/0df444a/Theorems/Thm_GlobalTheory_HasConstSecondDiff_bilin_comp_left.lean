-- Prove2me | Theorems.Thm_GlobalTheory_HasConstSecondDiff_bilin_comp_left
-- name    : GlobalTheory.HasConstSecondDiff.bilin_comp_left
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:06:55.624157+00:00
-- url     : https://prove2.me/theorems/64d6132d-89ef-48de-861c-2015a264c299
-- title:
--   Has Const Second Diff: bilin comp left
-- statement:
--   The Has Const Second Diff construction uses the bilin comp left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBimultiplicativeOfSecondQuotConst.lean#L107-L109
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBimultiplicativeOfSecondQuotConst.lean#L107-L109

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_ExistsBimultiplicativeOfSecondQuotConst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Module TensorProduct
open GlobalTheory
variable {X A : Type*} [AddCommGroup X] [AddCommGroup A]
open GlobalTheory.HasConstSecondDiff
variable {f : X → A}

theorem GlobalTheory.HasConstSecondDiff.bilin_comp_left {A' : Type*} [AddCommGroup A'] (h : HasConstSecondDiff f) (v : A →+ A')
    (μ ν : X) : (h.comp_left v).bilin μ ν = v (h.bilin μ ν) := by sorry
