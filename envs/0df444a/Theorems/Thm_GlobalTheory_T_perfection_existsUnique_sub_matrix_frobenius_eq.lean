-- Prove2me | Theorems.Thm_GlobalTheory_T_perfection_existsUnique_sub_matrix_frobenius_eq
-- name    : GlobalTheory.T.perfection_existsUnique_sub_matrix_frobenius_eq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:35:51.274803+00:00
-- url     : https://prove2.me/theorems/e5e44570-72c0-4460-94a9-7f531fac0e85
-- title:
--   T: perfection exists Unique sub matrix frobenius eq
-- statement:
--   The T construction uses the perfection exists Unique sub matrix frobenius eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PerfectionExistsUniqueSubMatrixFrobeniusEqStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/PerfectionExistsUniqueSubMatrixFrobeniusEqStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PerfectionExistsUniqueSubMatrixFrobeniusEq
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_PerfectionExistsUniqueSubMatrixFrobeniusEqStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.perfection_existsUnique_sub_matrix_frobenius_eq : ∀ (p : ℕ) [Fact p.Prime] (S : Type) [CommRing S] [CharP S p] (ι : Type) [Fintype ι] (Q : Matrix ι ι (Perfection S p)), (∀ n : ℕ, ∃ K : ℕ, ∀ z : ι → S, (fun w : ι → S => (Q.map (Perfection.coeff S p n)).mulVec fun k => frobenius S p (w k))^[K] z = 0) → ∀ c : ι → Perfection S p, ∃! x : ι → Perfection S p, x - Q.mulVec (fun k => frobenius (Perfection S p) p (x k)) = c := by sorry
