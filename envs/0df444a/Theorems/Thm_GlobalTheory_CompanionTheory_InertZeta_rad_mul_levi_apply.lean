-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertZeta_rad_mul_levi_apply
-- name    : GlobalTheory.CompanionTheory.InertZeta.rad_mul_levi_apply
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:02:42.444302+00:00
-- url     : https://prove2.me/theorems/81d9964d-08ad-4492-a451-a1d963f49750
-- title:
--   Inert Zeta: rad mul levi apply
-- statement:
--   The Inert Zeta construction uses the rad mul levi apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CosetInjective.lean#L14-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CosetInjective.lean#L14-L22

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_CosetInjective
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertZeta
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {n : ℕ}

theorem GlobalTheory.CompanionTheory.InertZeta.rad_mul_levi_apply {β : Fin n → ℕ} {u p : GU σ n} (hu : u ∈ radU σ β) (hp : p ∈ leviU σ β) {i j : Fin n}
    (hij : β j ≤ β i) : mat (u * p) i j = mat p i j := by sorry
