-- Prove2me | Theorems.Thm_GlobalTheory_frameMul_diagonal
-- name    : GlobalTheory.frameMul_diagonal
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:53:46.192579+00:00
-- url     : https://prove2.me/theorems/fd64f286-1450-402a-8906-6adb50a00bce
-- title:
--   Global Theory: frame Mul diagonal
-- statement:
--   The Global Theory construction uses the frame Mul diagonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsUnitEvalOfMapResidueNeZero.lean#L82-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsUnitEvalOfMapResidueNeZero.lean#L82-L85

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_ExistsIsUnitEvalOfMapResidueNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped BigOperators
open Module
open GlobalTheory
variable {ι : Type*} {K : Type*} {V : ι → Type*}
variable [CommSemiring K] [∀ s, AddCommMonoid (V s)] [∀ s, Module K (V s)]
  {l m n : ι → Type*} [∀ s, Fintype (l s)] [∀ s, Fintype (m s)]

theorem GlobalTheory.frameMul_diagonal [∀ s, DecidableEq (m s)] (x : ∀ s, m s → V s) (d : ∀ s, m s → K) :
    frameMul x (fun s => Matrix.diagonal (d s)) = fun s j => d s j • x s j := by sorry
