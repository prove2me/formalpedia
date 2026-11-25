-- Prove2me | Theorems.Thm_GlobalTheory_T_finrank_zmod_tensor_homology_zero_of_noPTorsion
-- name    : GlobalTheory.T.finrank_zmod_tensor_homology_zero_of_noPTorsion
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:31:06.796187+00:00
-- url     : https://prove2.me/theorems/8e237203-ec23-55e0-b0f8-a2578c37f1c4
-- title:
--   T: finrank zmod tensor homology zero of no PTorsion
-- statement:
--   The T construction uses the finrank zmod tensor homology zero of no PTorsion property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankZmodTensorHomologyZeroOfNoPTorsionStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/FinrankZmodTensorHomologyZeroOfNoPTorsionStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankZmodTensorHomologyZeroOfNoPTorsion
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FinrankZmodTensorHomologyZeroOfNoPTorsionStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.finrank_zmod_tensor_homology_zero_of_noPTorsion : ∀ (C : CochainComplex (ModuleCat.{0} ℤ) ℕ) (p : ℕ) [Fact p.Prime], (∀ (x : C.X 0), (p : ℤ) • x = 0 → x = 0) → Module.Finite ℤ (C.homology 0) → Module.finrank (ZMod p) (TensorProduct ℤ (ZMod p) (C.homology 0)) = Module.finrank ℤ (C.homology 0) := by sorry
