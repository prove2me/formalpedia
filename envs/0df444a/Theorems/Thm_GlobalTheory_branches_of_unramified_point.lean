-- Prove2me | Theorems.Thm_GlobalTheory_branches_of_unramified_point
-- name    : GlobalTheory.branches_of_unramified_point
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:08:39.47002+00:00
-- url     : https://prove2.me/theorems/36a75c30-df30-40c9-8904-60f54f2a3ae1
-- title:
--   Global Theory: branches of unramified point
-- statement:
--   The Global Theory construction uses the branches of unramified point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFormalBranchesOfSeparableReduction.lean#L46-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsFormalBranchesOfSeparableReduction.lean#L46-L84

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLiftsOfSeparableStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsFormalBranchesOfSeparableReduction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory
open GlobalTheory.ShiftHomomorphism

theorem GlobalTheory.branches_of_unramified_point : ∀ (D : ℕ) (P : Polynomial (MvPolynomial (Fin D) ℂ)) (c : Fin D → ℂ), P.Monic → (P.map (MvPolynomial.eval c)).Separable → ∃ (n : ℕ) (φ : Fin n → (AdjoinRoot P →ₐ[ℂ] MvPowerSeries (Fin D) ℂ)), (∀ u, (∀ j, φ j u = 0) → u = 0) ∧ ∀ j i, φ j (AdjoinRoot.of P (MvPolynomial.X i)) = MvPowerSeries.X i + MvPowerSeries.C (c i) := by sorry
