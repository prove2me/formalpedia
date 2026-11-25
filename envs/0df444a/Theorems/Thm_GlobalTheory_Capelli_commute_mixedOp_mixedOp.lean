-- Prove2me | Theorems.Thm_GlobalTheory_Capelli_commute_mixedOp_mixedOp
-- name    : GlobalTheory.Capelli.commute_mixedOp_mixedOp
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:58:10.960809+00:00
-- url     : https://prove2.me/theorems/9a206936-caca-4a5c-b6ee-938d60039e9d
-- title:
--   Capelli: commute mixed Op mixed Op
-- statement:
--   The Capelli construction uses the commute mixed Op mixed Op property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CommuteRowOpRightMixedOp.lean#L151-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CuspFormEvaluations/CommuteRowOpRightMixedOp.lean#L151-L158

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

theorem GlobalTheory.Capelli.commute_mixedOp_mixedOp {I₁ I₂ I₃ I₄ : Type*} [Fintype I₁] [Fintype I₂] [Fintype I₃]
    [Fintype I₄] (z : I₁ × J → σ) (y : I₂ × J → σ) (z' : I₃ × J' → σ) (y' : I₄ × J' → σ)
    (hzz : ∀ u w, z u ≠ z' w) (hzy : ∀ u w, z u ≠ y' w) (hyz : ∀ u w, y u ≠ z' w)
    (hyy : ∀ u w, y u ≠ y' w) (i j : J) (k l : J') :
    Commute (mixedOp K z y i j) (mixedOp K z' y' k l) := by sorry
