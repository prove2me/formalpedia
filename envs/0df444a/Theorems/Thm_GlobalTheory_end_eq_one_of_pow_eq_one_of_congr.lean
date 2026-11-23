-- Prove2me | Theorems.Thm_GlobalTheory_end_eq_one_of_pow_eq_one_of_congr
-- name    : GlobalTheory.end_eq_one_of_pow_eq_one_of_congr
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T14:45:48.558394+00:00
-- url     : https://prove2.me/theorems/bcc0fe0a-eff1-4438-b505-d58d1019da19
-- title:
--   Global Theory: end eq one of pow eq one of congr
-- statement:
--   The Global Theory construction uses the end eq one of pow eq one of congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsInvariantNatLengthLattice.lean#L57-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ThetaShiftProofs/ExistsInvariantNatLengthLattice.lean#L57-L99

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

theorem GlobalTheory.end_eq_one_of_pow_eq_one_of_congr (Y : Type*) [AddCommGroup Y] [Module.Free ℤ Y]
    [Module.Finite ℤ Y] (σ : Module.End ℤ Y) (n M : ℕ) (hn : 0 < n) (hσ : σ ^ n = 1) (hM : 3 ≤ M)
    (h : ∀ y, ∃ z, σ y = y + M • z) : σ = 1 := by sorry
