-- Prove2me | Theorems.Thm_GlobalTheory_T_jacobiTripleFiniteCoeff_tendsto_and_bounded
-- name    : GlobalTheory.T.jacobiTripleFiniteCoeff_tendsto_and_bounded
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-27T05:39:38.184265+00:00
-- url     : https://prove2.me/theorems/2c399c29-be65-41e0-9381-dd84ba923ff5
-- title:
--   T: jacobi Triple Finite Coeff tendsto and bounded
-- statement:
--   The T construction uses the jacobi Triple Finite Coeff tendsto and bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/JacobiTripleFiniteCoeffTendstoAndBoundedStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/JacobiTripleFiniteCoeffTendstoAndBoundedStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_JacobiTripleFiniteCoeffTendstoAndBounded
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MultipliableTpFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_JacobiTripleFiniteCoeffTendstoAndBoundedStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
open scoped Real
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.jacobiTripleFiniteCoeff_tendsto_and_bounded : ∀ t : ℂ, ‖t‖ < 1 → (∀ j : ℤ, Filter.Tendsto (fun n : ℕ => GlobalTheory.JacobiTriple.finCoeff t n j) Filter.atTop (nhds (GlobalTheory.JacobiTriple.qPochInf t)⁻¹)) ∧ ∃ C : ℝ, ∀ (n : ℕ) (j : ℤ), ‖GlobalTheory.JacobiTriple.finCoeff t n j‖ ≤ C := by sorry
