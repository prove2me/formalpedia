-- Prove2me | Theorems.Thm_GlobalTheory_HasConstSecondDiff_bilin_apply
-- name    : GlobalTheory.HasConstSecondDiff.bilin_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:57:54.198385+00:00
-- url     : https://prove2.me/theorems/d58e75a9-60ae-4569-9da2-5a226476df4b
-- title:
--   Has Const Second Diff: bilin apply
-- statement:
--   The Has Const Second Diff construction uses the bilin apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBimultiplicativeOfSecondQuotConst.lean#L51-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBimultiplicativeOfSecondQuotConst.lean#L51-L53

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

theorem GlobalTheory.HasConstSecondDiff.bilin_apply (h : HasConstSecondDiff f) (a μ ν : X) :
    h.bilin μ ν = f (a + μ + ν) - f (a + μ) - f (a + ν) + f a := by sorry
