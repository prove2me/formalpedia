-- Prove2me | Theorems.Thm_GlobalTheory_frameMul_frameMul
-- name    : GlobalTheory.frameMul_frameMul
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:53:33.944398+00:00
-- url     : https://prove2.me/theorems/172b0041-d7d1-4c9a-81bf-2d044812e64f
-- title:
--   Global Theory: frame Mul frame Mul
-- statement:
--   The Global Theory construction uses the frame Mul frame Mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsUnitEvalOfMapResidueNeZero.lean#L74-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/ExistsIsUnitEvalOfMapResidueNeZero.lean#L74-L80

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

theorem GlobalTheory.frameMul_frameMul (x : ∀ s, l s → V s) (b : ∀ s, Matrix (l s) (m s) K)
    (c : ∀ s, Matrix (m s) (n s) K) :
    frameMul (frameMul x b) c = frameMul x (fun s => b s * c s) := by sorry
