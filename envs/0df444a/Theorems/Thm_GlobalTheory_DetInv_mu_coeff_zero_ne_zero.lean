-- Prove2me | Theorems.Thm_GlobalTheory_DetInv_mu_coeff_zero_ne_zero
-- name    : GlobalTheory.DetInv.mu_coeff_zero_ne_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T12:49:27.584813+00:00
-- url     : https://prove2.me/theorems/4e02dc7f-a93a-4885-be0e-d697426ab7fa
-- title:
--   Det Inv: mu coeff zero ne zero
-- statement:
--   The Det Inv construction uses the mu coeff zero ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MuCoeffZeroNeZero.lean#L9-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/MuCoeffZeroNeZero.lean#L9-L36

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_IotaScalarOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_MuCoeffZeroNeZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
open GlobalTheory GlobalTheory.DetInv
open Matrix TensorProduct

theorem GlobalTheory.DetInv.mu_coeff_zero_ne_zero : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C]
    [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C]
    [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O →
    ∀ (ε : PreTilt O p), IsPrimitiveRoot (_root_.GlobalTheory.Sandwich.root ε).untilt p →
      (_root_.GlobalTheory.Sandwich.mu ε).coeff 0 ≠ 0 ∧ _root_.GlobalTheory.Sandwich.mu ε ≠ 0 ∧
        _root_.GlobalTheory.Sandwich.nu ε ≠ 0 := by sorry
