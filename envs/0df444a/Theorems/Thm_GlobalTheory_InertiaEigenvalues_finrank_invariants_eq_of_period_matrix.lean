-- Prove2me | Theorems.Thm_GlobalTheory_InertiaEigenvalues_finrank_invariants_eq_of_period_matrix
-- name    : GlobalTheory.InertiaEigenvalues.finrank_invariants_eq_of_period_matrix
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:19:34.433625+00:00
-- url     : https://prove2.me/theorems/2cdba36b-f232-4572-a6e1-8f7dcfef654f
-- title:
--   Inertia Eigenvalues: finrank invariants eq of period matrix
-- statement:
--   The Inertia Eigenvalues construction uses the finrank invariants eq of period matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinrankInvariantsEqOfInvertiblePeriodMatrix.lean#L6-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinrankInvariantsEqOfInvertiblePeriodMatrix.lean#L6-L67

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankInvariantsEqOfInvertiblePeriodMatrix
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
open Matrix

theorem GlobalTheory.InertiaEigenvalues.finrank_invariants_eq_of_period_matrix : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] (B : Type) [CommRing B] [Nontrivial B] [Algebra F B] [Algebra E B] [IsScalarTower F E B] (G : Type) (act : G → B →+* B) (n : Type) [Fintype n] [DecidableEq n] (A : G → Matrix n n B), (∀ b : B, (∀ g, act g b = b) ↔ ∃ c : E, algebraMap E B c = b) → ∀ Q : GL n B, (∀ g, A g * (Q : Matrix n n B).map (act g) = Q) → ∀ W : Submodule F (n → B), (∀ x, x ∈ W ↔ ∀ g, (A g).mulVec (fun i => act g (x i)) = x) → finrank F ↥W = finrank F E * Fintype.card n := by sorry
