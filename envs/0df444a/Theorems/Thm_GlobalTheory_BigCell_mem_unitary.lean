-- Prove2me | Theorems.Thm_GlobalTheory_BigCell_mem_unitary
-- name    : GlobalTheory.BigCell.mem_unitary
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:00:54.521632+00:00
-- url     : https://prove2.me/theorems/f54242d4-03ce-4114-9621-ed736d4213b8
-- title:
--   Big Cell: mem unitary
-- statement:
--   The Big Cell construction uses the mem unitary property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BigCellFactorisationDoubledUnitaryGroup.lean#L94-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/BigCellFactorisationDoubledUnitaryGroup.lean#L94-L125

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

theorem GlobalTheory.BigCell.mem_unitary (hG : Gᵀ * K * G.map f = K) (hΔT : Δᵀ = Δt) (hNT : Nᵀ = Nt) (hΔf : Δ.map f = Δ)
    (hΔtf : Δt.map f = Δt) (hNf : N.map f = N) (hNtf : Nt.map f = Nt)
    (e3 : Δt * K = J * Nt) (e4 : K * Δ = N * J) (e5 : Δt * K * Δ = 0)
    (e6 : Δ * J * Nt + N * J * Δt = (2 : R) • K) (e7 : Nt * K * N = 0) (hD : (Nt * G * N) * D' = 1) :
    (1 + ⅟(2 : R) • (Δ * (Δt * G * N * D') * Nt))ᵀ * K * (1 + ⅟(2 : R) • (Δ * (Δt * G * N * D') * Nt)).map f = K := by sorry
