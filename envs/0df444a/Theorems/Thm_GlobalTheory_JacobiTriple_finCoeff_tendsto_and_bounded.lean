-- Prove2me | Theorems.Thm_GlobalTheory_JacobiTriple_finCoeff_tendsto_and_bounded
-- name    : GlobalTheory.JacobiTriple.finCoeff_tendsto_and_bounded
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-27T05:38:07.336611+00:00
-- url     : https://prove2.me/theorems/3d9c02e2-bf32-4abb-8845-c3c254157371
-- title:
--   Jacobi Triple: fin Coeff tendsto and bounded
-- statement:
--   The Jacobi Triple construction uses the fin Coeff tendsto and bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/JacobiTripleFiniteCoeffTendstoAndBounded.lean#L11-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/JacobiTripleFiniteCoeffTendstoAndBounded.lean#L11-L57

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_MultipliableTpFactor
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_JacobiTripleFiniteCoeffTendstoAndBounded
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
noncomputable section
open GlobalTheory GlobalTheory.JacobiTriple

theorem GlobalTheory.JacobiTriple.finCoeff_tendsto_and_bounded :
    ∀ t : ℂ, ‖t‖ < 1 → (∀ j : ℤ, Filter.Tendsto (fun n : ℕ => GlobalTheory.JacobiTriple.finCoeff t n j)
      Filter.atTop (nhds (GlobalTheory.JacobiTriple.qPochInf t)⁻¹)) ∧
      ∃ C : ℝ, ∀ (n : ℕ) (j : ℤ), ‖GlobalTheory.JacobiTriple.finCoeff t n j‖ ≤ C := by sorry
