-- Prove2me | Theorems.Thm_GlobalTheory_exists_torsion_eq_prime_smul_of_noPTorsion
-- name    : GlobalTheory.exists_torsion_eq_prime_smul_of_noPTorsion
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:41:59.671804+00:00
-- url     : https://prove2.me/theorems/d80df983-7b64-4c89-bd3f-08e86b999ef1
-- title:
--   Global Theory: exists torsion eq prime smul of no PTorsion
-- statement:
--   The Global Theory construction uses the exists torsion eq prime smul of no PTorsion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankZmodTensorHomologyZeroOfNoPTorsion.lean#L6-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankZmodTensorHomologyZeroOfNoPTorsion.lean#L6-L45

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

theorem GlobalTheory.exists_torsion_eq_prime_smul_of_noPTorsion {M : Type*} [AddCommGroup M] (p : ℕ)
    [hp : Fact p.Prime] (hM : ∀ x : M, (p : ℤ) • x = 0 → x = 0) (t : M)
    (ht : t ∈ Submodule.torsion ℤ M) :
    ∃ s ∈ Submodule.torsion ℤ M, t = (p : ℤ) • s := by sorry
