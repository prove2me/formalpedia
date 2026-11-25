-- Prove2me | Theorems.Thm_GlobalTheory_T_invariantHermitianForm_nonneg_of_cloud_eigen
-- name    : GlobalTheory.T.invariantHermitianForm_nonneg_of_cloud_eigen
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T07:46:50.059037+00:00
-- url     : https://prove2.me/theorems/bb15079f-bf08-4a91-9b8c-54f7a77d10dd
-- title:
--   T: invariant Hermitian Form nonneg of cloud eigen
-- statement:
--   The T construction uses the invariant Hermitian Form nonneg of cloud eigen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/InvariantHermitianFormNonnegOfCloudEigenStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/InvariantHermitianFormNonnegOfCloudEigenStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_InvariantHermitianFormNonnegOfCloudEigen
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Jets_SumIoPr
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_InvariantHermitianFormNonnegOfCloudEigenStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.invariantHermitianForm_nonneg_of_cloud_eigen : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ) (x : Fin n → M), IsMod ε E μ → Shape ε kk μ bv → j ≤ 4 * n ^ 2 + 2 → (∀ c, Lev ε E μ j (x c)) → ∀ s : Fin n, s.val + 1 < kk → splitCas E x = ((-μ s + (1 - (n : ℝ)) / 2 : ℝ) : ℂ) • x → 0 ≤ (hhJ ε x x).re := by sorry
