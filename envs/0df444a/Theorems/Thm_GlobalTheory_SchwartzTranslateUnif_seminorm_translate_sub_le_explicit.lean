-- Prove2me | Theorems.Thm_GlobalTheory_SchwartzTranslateUnif_seminorm_translate_sub_le_explicit
-- name    : GlobalTheory.SchwartzTranslateUnif.seminorm_translate_sub_le_explicit
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:48:15.44394+00:00
-- url     : https://prove2.me/theorems/239251ad-3f52-4809-a414-ea0ce668b1c0
-- title:
--   Schwartz Translate Unif: seminorm translate sub le explicit
-- statement:
--   The Schwartz Translate Unif construction uses the seminorm translate sub le explicit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzTranslateTaylorSecondOrder.lean#L32-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/SchwartzTranslateTaylorSecondOrder.lean#L32-L100

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasTemperateGrowthProdMkConst
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzSeminormTranslateSubLineDerivLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SchwartzTranslateTaylorSecondOrder
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped SchwartzMap ContDiff
open GlobalTheory.SchwartzFstOp
open GlobalTheory GlobalTheory.SchwartzTranslateUnif
open GlobalTheory.SchwartzTranslate

theorem GlobalTheory.SchwartzTranslateUnif.seminorm_translate_sub_le_explicit {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a : V) (f : 𝓢(V, ℂ)) (k n : ℕ) (t : ℝ) (ht : |t| ≤ 1) :
    SchwartzMap.seminorm ℂ k n (SchwartzMap.compSubConstCLM ℂ (-(t • a)) f - f
        - (t : ℂ) • LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f)
      ≤ 2 ^ (k - 1) * (SchwartzMap.seminorm ℂ k n
            (LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a (LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f))
          + ‖a‖ ^ k * SchwartzMap.seminorm ℂ 0 n
            (LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a (LineDeriv.lineDerivOpCLM ℂ 𝓢(V, ℂ) a f)))
        * t ^ 2 := by sorry
