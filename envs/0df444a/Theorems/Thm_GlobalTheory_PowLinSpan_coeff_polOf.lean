-- Prove2me | Theorems.Thm_GlobalTheory_PowLinSpan_coeff_polOf
-- name    : GlobalTheory.PowLinSpan.coeff_polOf
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T18:51:45.037686+00:00
-- url     : https://prove2.me/theorems/d70ea6fc-860a-4976-b87b-9888c2f79208
-- title:
--   Pow Lin Span: coeff pol Of
-- statement:
--   The Pow Lin Span construction uses the coeff pol Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HomogeneousMemSpanLinearRoots.lean#L37-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HomogeneousMemSpanLinearRoots.lean#L37-L53

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

theorem GlobalTheory.PowLinSpan.coeff_polOf (φ : Module.Dual ℝ (MvPolynomial σ ℝ)) (d : ℕ) (m : σ →₀ ℕ) (hm : ∑ x, m x = d) :
    coeff m (polOf φ d) = (Nat.multinomial Finset.univ m : ℝ) * φ (monomial m 1) := by sorry
