-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertTrans_conj_mem_radU
-- name    : GlobalTheory.CompanionTheory.InertTrans.conj_mem_radU
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:03:12.298942+00:00
-- url     : https://prove2.me/theorems/be3fda62-b747-43c9-9907-443de7e9eba7
-- title:
--   Inert Trans: conj mem rad U
-- statement:
--   The Inert Trans construction uses the conj mem rad U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SphericalTransitiveOfLevi.lean#L12-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SphericalTransitiveOfLevi.lean#L12-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_SphericalTransitiveOfLevi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl GlobalTheory.InertZeta
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertTrans
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}

theorem GlobalTheory.CompanionTheory.InertTrans.conj_mem_radU {n : ℕ} {β : Fin n → ℕ} {m u : GU σ n} (hm : m ∈ leviU σ β) (hu : u ∈ radU σ β) :
    m * u * m⁻¹ ∈ radU σ β := by sorry
