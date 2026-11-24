-- Prove2me | Theorems.Thm_GlobalTheory_BigCell_skew
-- name    : GlobalTheory.BigCell.skew
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:01:09.21837+00:00
-- url     : https://prove2.me/theorems/76a93fb4-223f-4232-abe1-5f1061370d37
-- title:
--   Big Cell: skew
-- statement:
--   The Big Cell construction uses the skew property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BigCellFactorisationDoubledUnitaryGroup.lean#L56-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BigCellFactorisationDoubledUnitaryGroup.lean#L56-L85

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

theorem GlobalTheory.BigCell.skew (hG : Gᵀ * K * G.map f = K) (hΔT : Δᵀ = Δt) (hNT : Nᵀ = Nt) (hΔtf : Δt.map f = Δt) (hNf : N.map f = N)
    (hNtf : Nt.map f = Nt) (e6 : Δ * J * Nt + N * J * Δt = (2 : R) • K) (e7 : Nt * K * N = 0)
    (hD : (Nt * G * N) * D' = 1) :
    (Δt * G * N * D')ᵀ * J + J * (Δt * G * N * D').map f = 0 := by sorry
