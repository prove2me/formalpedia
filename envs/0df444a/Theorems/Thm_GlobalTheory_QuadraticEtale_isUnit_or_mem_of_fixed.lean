-- Prove2me | Theorems.Thm_GlobalTheory_QuadraticEtale_isUnit_or_mem_of_fixed
-- name    : GlobalTheory.QuadraticEtale.isUnit_or_mem_of_fixed
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T19:12:48.5829+00:00
-- url     : https://prove2.me/theorems/f7cb6a1b-b345-4892-8e9d-1e85beaad21a
-- title:
--   Quadratic Etale: is Unit or mem of fixed
-- statement:
--   The Quadratic Etale construction uses the is Unit or mem of fixed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsIsUnitFormSelfOfNotMem.lean#L30-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/ExistsIsUnitFormSelfOfNotMem.lean#L30-L36

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
variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] (σ : S →+* S)
variable [IsLocalRing R]

theorem GlobalTheory.QuadraticEtale.isUnit_or_mem_of_fixed (hfix : ∀ x, σ x = x → x ∈ (algebraMap R S).range)
    {x : S} (hx : σ x = x) :
    IsUnit x ∨ x ∈ (maximalIdeal R).map (algebraMap R S) := by sorry
