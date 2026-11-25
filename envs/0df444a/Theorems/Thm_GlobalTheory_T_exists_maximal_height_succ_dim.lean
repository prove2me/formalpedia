-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_maximal_height_succ_dim
-- name    : GlobalTheory.T.exists_maximal_height_succ_dim
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:30:16.819743+00:00
-- url     : https://prove2.me/theorems/885732f8-65ba-40c3-b9a6-8ffe676ad80f
-- title:
--   T: exists maximal height succ dim
-- statement:
--   The T construction uses the exists maximal height succ dim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMaximalHeightSuccDimStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsMaximalHeightSuccDimStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMaximalHeightSuccDim
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsMaximalHeightSuccDimStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_maximal_height_succ_dim : ∀ (k : Type) [CommRing k] [IsDomain k] [Module.Finite ℤ k] [CharZero k] (A : Type) [CommRing A] [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] [FaithfulSMul k A] (d : ℕ), ringKrullDim (FractionRing k ⊗[k] A) = d → ∃ M : Ideal A, M.IsMaximal ∧ ((d + 1 : ℕ) : ℕ∞) ≤ M.height := by sorry
