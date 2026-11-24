-- Prove2me | Theorems.Thm_GlobalTheory_FixedRoots_coeff_prod_mem
-- name    : GlobalTheory.FixedRoots.coeff_prod_mem
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T13:31:35.454477+00:00
-- url     : https://prove2.me/theorems/786cd2e5-f61e-46f2-9707-e7d330c9bfc1
-- title:
--   Fixed Roots: coeff prod mem
-- statement:
--   The Fixed Roots construction uses the coeff prod mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/MemOfForallRingEquivFixed.lean#L42-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/MemOfForallRingEquivFixed.lean#L42-L59

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

theorem GlobalTheory.FixedRoots.coeff_prod_mem {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (k : Subfield Ω)
    (S : Finset Ω) (hS : ∀ σ : Ω ≃+* Ω, (∀ a ∈ k, σ a = a) → ∀ x ∈ S, σ x ∈ S) (n : ℕ) :
    (∏ x ∈ S, (X - C x)).coeff n ∈ k := by sorry
