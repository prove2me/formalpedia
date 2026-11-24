-- Prove2me | Theorems.Thm_GlobalTheory_PowLinSpan_monomial_kill
-- name    : GlobalTheory.PowLinSpan.monomial_kill
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T18:52:39.458261+00:00
-- url     : https://prove2.me/theorems/5f7266d6-426d-4c19-a42a-37588459be16
-- title:
--   Pow Lin Span: monomial kill
-- statement:
--   The Pow Lin Span construction uses the monomial kill property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HomogeneousMemSpanLinearRoots.lean#L64-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HomogeneousMemSpanLinearRoots.lean#L64-L72

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

theorem GlobalTheory.PowLinSpan.monomial_kill (φ : Module.Dual ℝ (MvPolynomial σ ℝ)) (d : ℕ) (hP : polOf φ d = 0)
    (m : σ →₀ ℕ) (hm : ∑ x, m x = d) : φ (monomial m 1) = 0 := by sorry
