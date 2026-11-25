-- Prove2me | Theorems.Thm_GlobalTheory_FixedRoots_main
-- name    : GlobalTheory.FixedRoots.main
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:04:58.691233+00:00
-- url     : https://prove2.me/theorems/ddfbf2c2-6cb5-5a20-9659-665dd16c29c7
-- title:
--   Fixed Roots: main
-- statement:
--   The Fixed Roots construction uses the main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/MemOfForallRingEquivFixed.lean#L61-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/MemOfForallRingEquivFixed.lean#L61-L64

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_FixedByAutomorphismInField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsRingEquivAddOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MemOfForallRingEquivFixed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open GlobalTheory GlobalTheory.FixedRoots

theorem GlobalTheory.FixedRoots.main : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (k : Subfield Ω) (S : Finset Ω),
    (∀ σ : Ω ≃+* Ω, (∀ a ∈ k, σ a = a) → ∀ x ∈ S, σ x ∈ S) → ∀ n,
      (∏ x ∈ S, (X - C x)).coeff n ∈ k := by sorry
