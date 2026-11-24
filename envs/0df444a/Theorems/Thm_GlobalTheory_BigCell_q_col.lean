-- Prove2me | Theorems.Thm_GlobalTheory_BigCell_q_col
-- name    : GlobalTheory.BigCell.q_col
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:01:28.310574+00:00
-- url     : https://prove2.me/theorems/86017e19-962a-43ef-aba8-fd4c039fdf75
-- title:
--   Big Cell: q col
-- statement:
--   The Big Cell construction uses the q col property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BigCellFactorisationDoubledUnitaryGroup.lean#L142-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BigCellFactorisationDoubledUnitaryGroup.lean#L142-L151

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

theorem GlobalTheory.BigCell.q_col (h2 : Δ * Δt + N * Nt = (2 : R) • 1) (hD' : D' * (Nt * G * N) = 1) :
    (1 - ⅟(2 : R) • (Δ * (Δt * G * N * D') * Nt)) * G * N = N * (⅟(2 : R) • (Nt * G * N)) := by sorry
