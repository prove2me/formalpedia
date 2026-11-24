-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_formal_branches_of_separable_reduction
-- name    : GlobalTheory.T.exists_formal_branches_of_separable_reduction
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T21:40:34.593019+00:00
-- url     : https://prove2.me/theorems/21fac5b6-cce9-4b4a-9a77-1eaf018425a2
-- title:
--   T: exists formal branches of separable reduction
-- statement:
--   The T construction uses the exists formal branches of separable reduction property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFormalBranchesOfSeparableReductionStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFormalBranchesOfSeparableReductionStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFormalBranchesOfSeparableReduction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFormalBranchesOfSeparableReductionStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_formal_branches_of_separable_reduction : ∀ (D : ℕ) (P : Polynomial (MvPolynomial (Fin D) ℂ)) (c : Fin D → ℂ), P.Monic → (P.map (MvPolynomial.eval c)).Separable → ∃ (n : ℕ) (φ : Fin n → (AdjoinRoot P →ₐ[ℂ] MvPowerSeries (Fin D) ℂ)), (∀ u, (∀ j, φ j u = 0) → u = 0) ∧ ∀ j i, φ j (AdjoinRoot.of P (MvPolynomial.X i)) = MvPowerSeries.X i + MvPowerSeries.C (c i) := by sorry
