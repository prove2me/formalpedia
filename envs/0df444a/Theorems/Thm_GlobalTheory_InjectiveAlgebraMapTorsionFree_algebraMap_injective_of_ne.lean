-- Prove2me | Theorems.Thm_GlobalTheory_InjectiveAlgebraMapTorsionFree_algebraMap_injective_of_ne
-- name    : GlobalTheory.InjectiveAlgebraMapTorsionFree.algebraMap_injective_of_ne
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:19:19.269418+00:00
-- url     : https://prove2.me/theorems/0c47ecd7-6b0f-4582-8399-3a048eeffd96
-- title:
--   Injective Algebra Map Torsion Free: algebra Map injective of ne
-- statement:
--   The Injective Algebra Map Torsion Free construction uses the algebra Map injective of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsInjectiveNormLeOne.lean#L7-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/ExistsInjectiveNormLeOne.lean#L7-L17

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

theorem GlobalTheory.InjectiveAlgebraMapTorsionFree.algebraMap_injective_of_ne (D : Type) [CommRing D] [IsDomain D] [Algebra ℤ_[p] D]
    (hp : (p : D) ≠ 0) : Function.Injective (algebraMap ℤ_[p] D) := by sorry
