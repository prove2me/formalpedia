-- Prove2me | Theorems.Thm_GlobalTheory_InjectiveAlgebraMapTorsionFree_exists_injective_norm_le_one
-- name    : GlobalTheory.InjectiveAlgebraMapTorsionFree.exists_injective_norm_le_one
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:19:10.141842+00:00
-- url     : https://prove2.me/theorems/c5dc5a03-8d2f-443e-9282-371aed984a53
-- title:
--   Injective Algebra Map Torsion Free: exists injective norm le one
-- statement:
--   The Injective Algebra Map Torsion Free construction uses the exists injective norm le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsInjectiveNormLeOne.lean#L59-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsInjectiveNormLeOne.lean#L59-L77

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsInjectiveNormLeOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.InjectiveAlgebraMapTorsionFree
variable (p : ℕ) [Fact (Nat.Prime p)]

theorem GlobalTheory.InjectiveAlgebraMapTorsionFree.exists_injective_norm_le_one (p : ℕ) [Fact (Nat.Prime p)] (D : Type) [CommRing D]
    [IsDomain D] [Algebra ℤ_[p] D] [Module.Finite ℤ_[p] D] (hp : (p : D) ≠ 0) :
    ∃ φ : D →+* PadicAlgCl p, Function.Injective φ ∧ ∀ d : D, ‖φ d‖ ≤ 1 := by sorry
