-- Prove2me | Theorems.Thm_GlobalTheory_CharFormDeriv_hasTemperateGrowth_char
-- name    : GlobalTheory.CharFormDeriv.hasTemperateGrowth_char
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:21:14.515945+00:00
-- url     : https://prove2.me/theorems/9acd835f-f73d-400b-a651-180d8b70be86
-- title:
--   Char Form Deriv: has Temperate Growth char
-- statement:
--   The Char Form Deriv construction uses the has Temperate Growth char property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivRemCompLe.lean#L150-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormIteratedFDerivRemCompLe.lean#L150-L170

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIteratedFDerivRemCompLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open GlobalTheory GlobalTheory.CharFormDeriv

theorem GlobalTheory.CharFormDeriv.hasTemperateGrowth_char {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (L : V →L[ℝ] ℝ) (t : ℝ) :
    Function.HasTemperateGrowth (fun x : V => Complex.exp ((I * t) * (L x : ℂ))) := by sorry
