-- Prove2me | Theorems.Thm_GlobalTheory_PowLinSpan_degreeOf_polOf_le
-- name    : GlobalTheory.PowLinSpan.degreeOf_polOf_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:51:29.976294+00:00
-- url     : https://prove2.me/theorems/6e8f49e7-449f-4a17-84dc-bc8f7fd3233b
-- title:
--   Pow Lin Span: degree Of pol Of le
-- statement:
--   The Pow Lin Span construction uses the degree Of pol Of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HomogeneousMemSpanLinearRoots.lean#L55-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HomogeneousMemSpanLinearRoots.lean#L55-L62

import Mathlib
import Definitions.Def_Formalism_DegreeFormula_FlagDegFormula
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HomogeneousMemSpanLinearRoots
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open GlobalTheory
open GlobalTheory.PowLinSpan
variable {σ : Type} [Fintype σ] [DecidableEq σ]

theorem GlobalTheory.PowLinSpan.degreeOf_polOf_le (φ : Module.Dual ℝ (MvPolynomial σ ℝ)) (d : ℕ) (x : σ) :
    (polOf φ d).degreeOf x ≤ d := by sorry
