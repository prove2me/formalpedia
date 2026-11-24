-- Prove2me | Theorems.Thm_GlobalTheory_T_finrank_invariants_eq_of_invertible_periodMatrix
-- name    : GlobalTheory.T.finrank_invariants_eq_of_invertible_periodMatrix
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T20:39:13.528807+00:00
-- url     : https://prove2.me/theorems/39b8636d-1434-4367-881c-8c243a23755a
-- title:
--   T: finrank invariants eq of invertible period Matrix
-- statement:
--   The T construction uses the finrank invariants eq of invertible period Matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinrankInvariantsEqOfInvertiblePeriodMatrixStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/FinrankInvariantsEqOfInvertiblePeriodMatrixStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankInvariantsEqOfInvertiblePeriodMatrix
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_FinrankInvariantsEqOfInvertiblePeriodMatrixStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.finrank_invariants_eq_of_invertible_periodMatrix : ∀ (F E : Type) [Field F] [Field E] [Algebra F E] [FiniteDimensional F E] (B : Type) [CommRing B] [Nontrivial B] [Algebra F B] [Algebra E B] [IsScalarTower F E B] (G : Type) (act : G → B →+* B) (n : Type) [Fintype n] [DecidableEq n] (A : G → Matrix n n B), (∀ b : B, (∀ g, act g b = b) ↔ ∃ c : E, algebraMap E B c = b) → ∀ Q : GL n B, (∀ g, A g * (Q : Matrix n n B).map (act g) = Q) → ∀ W : Submodule F (n → B), (∀ x, x ∈ W ↔ ∀ g, (A g).mulVec (fun i => act g (x i)) = x) → finrank F ↥W = finrank F E * Fintype.card n := by sorry
