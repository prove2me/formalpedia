-- Prove2me | Theorems.Thm_GlobalTheory_subsingleton_zmod_tensor_torsion
-- name    : GlobalTheory.subsingleton_zmod_tensor_torsion
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:21:19.8098+00:00
-- url     : https://prove2.me/theorems/b885af3e-1950-4579-8ee4-f09d02abd1bf
-- title:
--   Global Theory: subsingleton zmod tensor torsion
-- statement:
--   The Global Theory construction uses the subsingleton zmod tensor torsion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankZmodTensorHomologyZeroOfNoPTorsion.lean#L47-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankZmodTensorHomologyZeroOfNoPTorsion.lean#L47-L60

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

theorem GlobalTheory.subsingleton_zmod_tensor_torsion {M : Type*} [AddCommGroup M] (p : ℕ) [Fact p.Prime]
    (hM : ∀ x : M, (p : ℤ) • x = 0 → x = 0) :
    Subsingleton (TensorProduct ℤ (ZMod p) (Submodule.torsion ℤ M)) := by sorry
