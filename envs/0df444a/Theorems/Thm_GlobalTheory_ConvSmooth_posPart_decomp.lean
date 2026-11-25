-- Prove2me | Theorems.Thm_GlobalTheory_ConvSmooth_posPart_decomp
-- name    : GlobalTheory.ConvSmooth.posPart_decomp
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T02:39:05.994093+00:00
-- url     : https://prove2.me/theorems/8e1ef6a9-1d33-4995-81e4-8b8eb9d2b15b
-- title:
--   Conv Smooth: pos Part decomp
-- statement:
--   The Conv Smooth construction uses the pos Part decomp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConvSmoothCompactSupport.lean#L47-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ConvSmoothCompactSupport.lean#L47-L51

import Mathlib
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_Casimir
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraRegularity_ExpHaar
import Definitions.Def_GroundTheory_AutomorphicForms_HarishChandraInvariance_Compact
import Definitions.Def_GroundTheory_AutomorphicForms_DixmierMalliavin
import Definitions.Def_GroundTheory_AutomorphicForms_GKModules_ParametricIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_LintegralInvLeOfSupportCompactStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IsSmoothFunIntegralMulRightStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ConvSmoothCompactSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GroundTheory.Automorphic
open scoped ContDiff
open GlobalTheory GlobalTheory.ConvSmooth

theorem GlobalTheory.ConvSmooth.posPart_decomp (w : ℂ) :
    w = (((Real.toNNReal w.re : NNReal) : ℝ) : ℂ) - (((Real.toNNReal (-w.re) : NNReal) : ℝ) : ℂ) +
      Complex.I * ((((Real.toNNReal w.im : NNReal) : ℝ) : ℂ) -
        (((Real.toNNReal (-w.im) : NNReal) : ℝ) : ℂ)) := by sorry
