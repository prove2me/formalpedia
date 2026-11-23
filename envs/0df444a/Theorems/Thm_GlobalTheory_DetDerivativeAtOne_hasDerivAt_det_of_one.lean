-- Prove2me | Theorems.Thm_GlobalTheory_DetDerivativeAtOne_hasDerivAt_det_of_one
-- name    : GlobalTheory.DetDerivativeAtOne.hasDerivAt_det_of_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:45:46.14913+00:00
-- url     : https://prove2.me/theorems/24691022-34b6-462f-8147-9c184d93e766
-- title:
--   Det Derivative At One: has Deriv At det of one
-- statement:
--   The Det Derivative At One construction uses the has Deriv At det of one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/HasDerivAtDetOfOne.lean#L7-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/HasDerivAtDetOfOne.lean#L7-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_HasDerivAtDetOfOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.DetDerivativeAtOne
open Equiv Finset

theorem GlobalTheory.DetDerivativeAtOne.hasDerivAt_det_of_one {n : Type} [Fintype n] [DecidableEq n]
    (A : ℝ → Matrix n n ℂ) (A' : Matrix n n ℂ) (h0 : A (0 : ℝ) = (1 : Matrix n n ℂ))
    (hd : ∀ (i j : n), HasDerivAt (fun (t : ℝ) ↦ A t i j) (A' i j) (0 : ℝ)) :
    HasDerivAt (fun (t : ℝ) ↦ Matrix.det (A t)) (Matrix.trace A') (0 : ℝ) := by sorry
