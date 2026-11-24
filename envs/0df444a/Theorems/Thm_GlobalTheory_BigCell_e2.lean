-- Prove2me | Theorems.Thm_GlobalTheory_BigCell_e2
-- name    : GlobalTheory.BigCell.e2
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:01:06.900836+00:00
-- url     : https://prove2.me/theorems/6da86f3f-6a27-4a0e-8019-87e1e2708d9c
-- title:
--   Big Cell: e2
-- statement:
--   The Big Cell construction uses the e2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BigCellFactorisationDoubledUnitaryGroup.lean#L15-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BigCellFactorisationDoubledUnitaryGroup.lean#L15-L19

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

theorem GlobalTheory.BigCell.e2 : (fromRows (1 : Matrix β β R) 1 : Matrix (β ⊕ β) β R) * (fromCols (1 : Matrix β β R) 1 : Matrix β (β ⊕ β) R) +
    (fromRows (1 : Matrix β β R) (-1) : Matrix (β ⊕ β) β R) * (fromCols (1 : Matrix β β R) (-1) : Matrix β (β ⊕ β) R) =
    (2 : R) • (1 : Matrix (β ⊕ β) (β ⊕ β) R) := by sorry
