-- Prove2me | Theorems.Thm_GlobalTheory_hasConstSecondDiff_iff
-- name    : GlobalTheory.hasConstSecondDiff_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:03:24.864411+00:00
-- url     : https://prove2.me/theorems/1c4c8954-5547-40af-b964-5ca909d2108c
-- title:
--   Global Theory: has Const Second Diff iff
-- statement:
--   The Global Theory construction uses the has Const Second Diff iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBimultiplicativeOfSecondQuotConst.lean#L30-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBimultiplicativeOfSecondQuotConst.lean#L30-L35

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

theorem GlobalTheory.hasConstSecondDiff_iff (f : X → A) :
    HasConstSecondDiff f ↔ ∀ a μ ν : X,
      f (a + μ + ν) - f (a + μ) - f (a + ν) + f a = f (μ + ν) - f μ - f ν + f 0 := by sorry
