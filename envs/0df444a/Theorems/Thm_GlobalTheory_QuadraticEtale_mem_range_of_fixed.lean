-- Prove2me | Theorems.Thm_GlobalTheory_QuadraticEtale_mem_range_of_fixed
-- name    : GlobalTheory.QuadraticEtale.mem_range_of_fixed
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:19:34.377864+00:00
-- url     : https://prove2.me/theorems/f0695e82-67ef-48b4-b47f-46eeb8daf898
-- title:
--   Quadratic Etale: mem range of fixed
-- statement:
--   The Quadratic Etale construction uses the mem range of fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsIsUnitFormSelfOfNotMem.lean#L334-L341
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsIsUnitFormSelfOfNotMem.lean#L334-L341

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_ExistsIsUnitFormSelfOfNotMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory GlobalTheory.QuadraticEtale
open Module
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R]
  [Module.Free R S] [Algebra.FormallyUnramified R S]

theorem GlobalTheory.QuadraticEtale.mem_range_of_fixed (hrank : finrank R S = 2) (σ : S ≃ₐ[R] S) (hσ : σ ≠ 1) (x : S)
    (hx : σ x = x) : x ∈ (algebraMap R S).range := by sorry
