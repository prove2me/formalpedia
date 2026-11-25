-- Prove2me | Theorems.Thm_GlobalTheory_T_height_maximal_le_prime_add_dim
-- name    : GlobalTheory.T.height_maximal_le_prime_add_dim
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:33:23.956572+00:00
-- url     : https://prove2.me/theorems/1db4483f-0572-4775-a88d-a199ca0281b1
-- title:
--   T: height maximal le prime add dim
-- statement:
--   The T construction uses the height maximal le prime add dim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeightMaximalLePrimeAddDimStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeightMaximalLePrimeAddDimStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeightMaximalLePrimeAddDim
import Mathlib
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_PolynomialHeights_PolyCM
import Definitions.Def_ReciprocityTheory_CommutativeAlgebra_CohenMacaulay_Bridge
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeightMaximalLePrimeAddDimStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.height_maximal_le_prime_add_dim : ∀ (A : Type) [CommRing A] [IsDomain A] [Algebra.FiniteType ℤ A] (P M : Ideal A) [P.IsPrime] [M.IsMaximal], (M.height : WithBot ℕ∞) ≤ (P.height : WithBot ℕ∞) + ringKrullDim (A ⧸ P) := by sorry
