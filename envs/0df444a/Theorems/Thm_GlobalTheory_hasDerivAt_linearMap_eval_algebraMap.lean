-- Prove2me | Theorems.Thm_GlobalTheory_hasDerivAt_linearMap_eval_algebraMap
-- name    : GlobalTheory.hasDerivAt_linearMap_eval_algebraMap
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:54:08.729709+00:00
-- url     : https://prove2.me/theorems/acdb1d41-3505-44d7-8350-a838c2b32fff
-- title:
--   Global Theory: has Deriv At linear Map eval algebra Map
-- statement:
--   The Global Theory construction uses the has Deriv At linear Map eval algebra Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasDerivAtLinearMapEvalAlgebraMap.lean#L9-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasDerivAtLinearMapEvalAlgebraMap.lean#L9-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasDerivAtLinearMapEvalAlgebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
open Polynomial

theorem GlobalTheory.hasDerivAt_linearMap_eval_algebraMap {A : Type*} [CommRing A] [Algebra ℝ A]
    (Φ : A →ₗ[ℝ] ℝ) (R : Polynomial A) (τ : ℝ) :
    HasDerivAt (fun t : ℝ => Φ (R.eval (algebraMap ℝ A t)))
      (Φ ((derivative R).eval (algebraMap ℝ A τ))) τ := by sorry
