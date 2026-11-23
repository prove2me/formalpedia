-- Prove2me | Theorems.Thm_GlobalTheory_SchwartzTranslate_fderiv_iteratedFDeriv_apply_comm
-- name    : GlobalTheory.SchwartzTranslate.fderiv_iteratedFDeriv_apply_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:35:22.470038+00:00
-- url     : https://prove2.me/theorems/f4b4111d-99f8-4f82-8ce5-ea1d4c6f6bdf
-- title:
--   Schwartz Translate: fderiv iterated FDeriv apply comm
-- statement:
--   The Schwartz Translate construction uses the fderiv iterated FDeriv apply comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzSeminormTranslateSubLineDerivLe.lean#L35-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzSeminormTranslateSubLineDerivLe.lean#L35-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSeminormTranslateSubLineDerivLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap ContDiff
open GlobalTheory GlobalTheory.SchwartzTranslate

theorem GlobalTheory.SchwartzTranslate.fderiv_iteratedFDeriv_apply_comm {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (a : V) (n : ℕ) :
    ∀ (g : V → F), ContDiff ℝ ∞ g → ∀ (x : V) (m : Fin n → V),
      fderiv ℝ (fun y => iteratedFDeriv ℝ n g y m) x a
        = iteratedFDeriv ℝ n (fun y => fderiv ℝ g y a) x m := by sorry
