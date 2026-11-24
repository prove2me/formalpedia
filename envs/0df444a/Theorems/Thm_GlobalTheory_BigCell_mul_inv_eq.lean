-- Prove2me | Theorems.Thm_GlobalTheory_BigCell_mul_inv_eq
-- name    : GlobalTheory.BigCell.mul_inv_eq
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:01:17.84108+00:00
-- url     : https://prove2.me/theorems/c7c66be2-6ab5-47cb-a7ae-d5d57201f257
-- title:
--   Big Cell: mul inv eq
-- statement:
--   The Big Cell construction uses the mul inv eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BigCellFactorisationDoubledUnitaryGroup.lean#L127-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BigCellFactorisationDoubledUnitaryGroup.lean#L127-L140

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_HilbertNinetyQuotientHomEqIff
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_BigCellFactorisationDoubledUnitaryGroup
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.WeilM
open scoped Matrix
open Matrix
open GlobalTheory GlobalTheory.BigCell
variable {R : Type} [CommRing R] {β : Type} [Fintype β] [DecidableEq β]
variable [Invertible (2 : R)]
variable (f : R →+* R) (J : Matrix β β R) (K G : Matrix (β ⊕ β) (β ⊕ β) R) (Δ N : Matrix (β ⊕ β) β R)
  (Δt Nt : Matrix β (β ⊕ β) R) (D' : Matrix β β R)

theorem GlobalTheory.BigCell.mul_inv_eq (hNtΔ : Nt * Δ = 0) (x : Matrix β β R) :
    (1 + ⅟(2 : R) • (Δ * x * Nt)) * (1 - ⅟(2 : R) • (Δ * x * Nt)) = 1 ∧
    (1 - ⅟(2 : R) • (Δ * x * Nt)) * (1 + ⅟(2 : R) • (Δ * x * Nt)) = 1 := by sorry
