-- Prove2me | Theorems.Thm_GlobalTheory_T_sum_smul_multilinear_eq_zero_of_prod_vanish
-- name    : GlobalTheory.T.sum_smul_multilinear_eq_zero_of_prod_vanish
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:39:01.09203+00:00
-- url     : https://prove2.me/theorems/16b690a1-1572-54e4-9383-abea387a8670
-- title:
--   T: sum smul multilinear eq zero of prod vanish
-- statement:
--   The T construction uses the sum smul multilinear eq zero of prod vanish property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MultilinearVanishOfProdVanishStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MultilinearVanishOfProdVanishStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MultilinearVanishOfProdVanish
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MultilinearVanishOfProdVanishStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.sum_smul_multilinear_eq_zero_of_prod_vanish : ∀ {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {X : ι → Type} (A : ∀ i, Submodule K (X i → K)) {M : Type} [AddCommGroup M] [Module K M] (P : MultilinearMap K (fun i => A i) M) {D : Type} (s : Finset D) (c : D → K) (f : D → ∀ i, A i), (∀ x : ∀ i, X i, ∑ d ∈ s, c d * ∏ i, (f d i : X i → K) (x i) = 0) → ∑ d ∈ s, c d • P (f d) = 0 := by sorry
