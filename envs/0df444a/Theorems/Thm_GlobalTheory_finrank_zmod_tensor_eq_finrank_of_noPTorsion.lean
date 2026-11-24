-- Prove2me | Theorems.Thm_GlobalTheory_finrank_zmod_tensor_eq_finrank_of_noPTorsion
-- name    : GlobalTheory.finrank_zmod_tensor_eq_finrank_of_noPTorsion
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:51:03.26135+00:00
-- url     : https://prove2.me/theorems/fec54226-69ad-406b-9ea1-5b40468b93b2
-- title:
--   Global Theory: finrank zmod tensor eq finrank of no PTorsion
-- statement:
--   The Global Theory construction uses the finrank zmod tensor eq finrank of no PTorsion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankZmodTensorHomologyZeroOfNoPTorsion.lean#L62-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankZmodTensorHomologyZeroOfNoPTorsion.lean#L62-L81

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankZmodTensorHomologyZeroOfNoPTorsion
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
open GlobalTheory

theorem GlobalTheory.finrank_zmod_tensor_eq_finrank_of_noPTorsion (M : Type*) [AddCommGroup M] [inst : Module ℤ M]
    [Module.Finite ℤ M] (p : ℕ) [Fact p.Prime] (hM : ∀ x : M, (p : ℤ) • x = 0 → x = 0) :
    Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) M) = Module.finrank ℤ M := by sorry
