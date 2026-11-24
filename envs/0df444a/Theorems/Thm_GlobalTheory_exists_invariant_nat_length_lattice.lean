-- Prove2me | Theorems.Thm_GlobalTheory_exists_invariant_nat_length_lattice
-- name    : GlobalTheory.exists_invariant_nat_length_lattice
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T22:33:53.407149+00:00
-- url     : https://prove2.me/theorems/b5898d9e-3a72-4601-b9dc-09d8e2275284
-- title:
--   Global Theory: exists invariant nat length lattice
-- statement:
--   The Global Theory construction uses the exists invariant nat length lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsInvariantNatLengthLattice.lean#L27-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsInvariantNatLengthLattice.lean#L27-L55

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_DataRigidTorsionOfDataRigid
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ThetaShiftProofs_ExistsInvariantNatLengthLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory

theorem GlobalTheory.exists_invariant_nat_length_lattice (Y : Type*) [AddCommGroup Y] [Module.Free ℤ Y]
    [Module.Finite ℤ Y] (σ : Module.End ℤ Y) (n : ℕ) (hn : 0 < n) (hσ : σ ^ n = 1) :
    ∃ p : Y → ℕ, (∀ x y, p (x - y) ≤ p x + p y) ∧ (∀ (m : ℕ) y, p (m • y) = m * p y) ∧
      (∀ y, p y = 0 → y = 0) ∧ ∀ y, p (σ y) = p y := by sorry
