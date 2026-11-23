-- Prove2me | Theorems.Thm_GlobalTheory_SchwartzTranslate_hasDerivAt_iteratedFDeriv_line
-- name    : GlobalTheory.SchwartzTranslate.hasDerivAt_iteratedFDeriv_line
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:35:37.113576+00:00
-- url     : https://prove2.me/theorems/4a65af44-4979-4116-953e-f195a599a0c5
-- title:
--   Schwartz Translate: has Deriv At iterated FDeriv line
-- statement:
--   The Schwartz Translate construction uses the has Deriv At iterated FDeriv line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzSeminormTranslateSubLineDerivLe.lean#L42-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzSeminormTranslateSubLineDerivLe.lean#L42-L57

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

theorem GlobalTheory.SchwartzTranslate.hasDerivAt_iteratedFDeriv_line {V F : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (a : V) (n : ℕ) (g : V → F) (hg : ContDiff ℝ ∞ g)
    (x : V) (s : ℝ) :
    HasDerivAt (fun s : ℝ => iteratedFDeriv ℝ n g (x + s • a))
      (iteratedFDeriv ℝ n (fun y => fderiv ℝ g y a) (x + s • a)) s := by sorry
