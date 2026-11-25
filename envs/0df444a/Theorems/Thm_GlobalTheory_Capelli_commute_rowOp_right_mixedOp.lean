-- Prove2me | Theorems.Thm_GlobalTheory_Capelli_commute_rowOp_right_mixedOp
-- name    : GlobalTheory.Capelli.commute_rowOp_right_mixedOp
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:58:22.860917+00:00
-- url     : https://prove2.me/theorems/111172c2-d955-4b32-8948-cfba9b5e78b7
-- title:
--   Capelli: commute row Op right mixed Op
-- statement:
--   The Capelli construction uses the commute row Op right mixed Op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CommuteRowOpRightMixedOp.lean#L165-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CommuteRowOpRightMixedOp.lean#L165-L169

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CuspFormEvaluations_CommuteRowOpRightMixedOp
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory GlobalTheory.Capelli
variable {K σ : Type*} [CommRing K]
variable {I J I' J' : Type*}

theorem GlobalTheory.Capelli.commute_rowOp_right_mixedOp [Fintype I] [Fintype I'] [Fintype J] (z : I × J → σ)
    (y : I' × J → σ) (hy : Function.Injective y) (hzy : ∀ u w, z u ≠ y w) (a b : I') (k l : J) :
    Commute (rowOp K y a b) (mixedOp K z y k l) := by sorry
