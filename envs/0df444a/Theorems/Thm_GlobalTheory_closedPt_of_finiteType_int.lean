-- Prove2me | Theorems.Thm_GlobalTheory_closedPt_of_finiteType_int
-- name    : GlobalTheory.closedPt_of_finiteType_int
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:08:33.925866+00:00
-- url     : https://prove2.me/theorems/c5fdc799-e6f3-4634-8492-859b3a5288a8
-- title:
--   Global Theory: closed Pt of finite Type int
-- statement:
--   The Global Theory construction uses the closed Pt of finite Type int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMaximalPrimeCharNotMemFiniteTypeInt.lean#L19-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMaximalPrimeCharNotMemFiniteTypeInt.lean#L19-L65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMaximalPrimeCharNotMemFiniteTypeInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.closedPt_of_finiteType_int : ∀ (R : Type) [CommRing R] [IsDomain R] [Algebra.FiniteType ℤ R] (f : R), f ≠ 0 → ∃ M : Ideal R, M.IsMaximal ∧ f ∉ M ∧ ∃ p : ℕ, p.Prime ∧ (p : R) ∈ M := by sorry
