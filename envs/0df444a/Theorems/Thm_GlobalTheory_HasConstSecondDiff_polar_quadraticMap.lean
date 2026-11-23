-- Prove2me | Theorems.Thm_GlobalTheory_HasConstSecondDiff_polar_quadraticMap
-- name    : GlobalTheory.HasConstSecondDiff.polar_quadraticMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:58:00.220525+00:00
-- url     : https://prove2.me/theorems/a3b6d497-1804-4cd8-a084-11d59adab007
-- title:
--   Has Const Second Diff: polar quadratic Map
-- statement:
--   The Has Const Second Diff construction uses the polar quadratic Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBimultiplicativeOfSecondQuotConst.lean#L94-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/ExistsBimultiplicativeOfSecondQuotConst.lean#L94-L97

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

theorem GlobalTheory.HasConstSecondDiff.polar_quadraticMap (h : HasConstSecondDiff f) (he : ∀ x, f (-x) = f x) (μ ν : X) :
    QuadraticMap.polar (h.quadraticMap he) μ ν = h.bilin μ ν := by sorry
