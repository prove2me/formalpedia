-- Prove2me | Theorems.Thm_GlobalTheory_BigCell_bigCell_factor
-- name    : GlobalTheory.BigCell.bigCell_factor
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:01:03.323844+00:00
-- url     : https://prove2.me/theorems/5a267833-9c0b-41df-bcfe-4f2ddc2321b3
-- title:
--   Big Cell: big Cell factor
-- statement:
--   The Big Cell construction uses the big Cell factor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BigCellFactorisationDoubledUnitaryGroup.lean#L155-L203
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BigCellFactorisationDoubledUnitaryGroup.lean#L155-L203

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

theorem GlobalTheory.BigCell.bigCell_factor : ∀ (A R : Type) [CommRing A] [CommRing R] [Algebra A R] (c : R →ₐ[A] R) [Invertible (2 : R)]
    (β : Type) [Fintype β] [DecidableEq β] (J : Matrix β β R) (g : UG c (dbl J)),
    IsUnit (Matrix.fromCols (1 : Matrix β β R) (-1 : Matrix β β R) * ((g : GL (β ⊕ β) R) : Matrix (β ⊕ β) (β ⊕ β) R) *
      Matrix.fromRows (1 : Matrix β β R) (-1 : Matrix β β R)).det →
    ∃ (p q : UG c (dbl J)) (t s : GL β R),
      ((p : GL (β ⊕ β) R) : Matrix (β ⊕ β) (β ⊕ β) R) * Matrix.fromRows (1 : Matrix β β R) (1 : Matrix β β R) =
        Matrix.fromRows (1 : Matrix β β R) (1 : Matrix β β R) * (t : Matrix β β R) ∧
      ((q : GL (β ⊕ β) R) : Matrix (β ⊕ β) (β ⊕ β) R) * Matrix.fromRows (1 : Matrix β β R) (-1 : Matrix β β R) =
        Matrix.fromRows (1 : Matrix β β R) (-1 : Matrix β β R) * (s : Matrix β β R) ∧ g = p * q := by sorry
