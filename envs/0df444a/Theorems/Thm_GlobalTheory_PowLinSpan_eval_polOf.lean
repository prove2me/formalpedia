-- Prove2me | Theorems.Thm_GlobalTheory_PowLinSpan_eval_polOf
-- name    : GlobalTheory.PowLinSpan.eval_polOf
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:51:45.816653+00:00
-- url     : https://prove2.me/theorems/aec373f1-6863-4901-93b7-b912d59d6e63
-- title:
--   Pow Lin Span: eval pol Of
-- statement:
--   The Pow Lin Span construction uses the eval pol Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HomogeneousMemSpanLinearRoots.lean#L29-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HomogeneousMemSpanLinearRoots.lean#L29-L35

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

theorem GlobalTheory.PowLinSpan.eval_polOf (φ : Module.Dual ℝ (MvPolynomial σ ℝ)) (d : ℕ) (u : σ → ℝ) :
    eval u (polOf φ d) = φ ((∑ x, C (u x) * X x) ^ d) := by sorry
