-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertCorner_defect_eq
-- name    : GlobalTheory.CompanionTheory.InertCorner.defect_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:00:13.223858+00:00
-- url     : https://prove2.me/theorems/a39367a4-4e62-42e3-9b09-73788e1e6dd1
-- title:
--   Inert Corner: defect eq
-- statement:
--   The Inert Corner construction uses the defect eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SmallCornerOfHeisenbergDual.lean#L147-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/SmallCornerOfHeisenbergDual.lean#L147-L164

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_SmallCornerOfHeisenbergDual
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertCorner
variable {L : Type} [Field L] {N : ℕ}
variable [Valued L (WithZero (Multiplicative ℤ))]

theorem GlobalTheory.CompanionTheory.InertCorner.defect_eq {σ : L →+* L} (g₀ : GU σ N) {U V C : Matrix (Fin N) (Fin N) L}
    (hC : (U + V * mat g₀) * C = 1) :
    -((U + V * mat g₀) * 1 * st σ (U + V * mat g₀)) + (U + V * mat g₀) * (C * V * mat g₀) * st σ (U + V * mat g₀)
      + (U + V * mat g₀) * st σ (C * V * mat g₀) * st σ (U + V * mat g₀)
      = -(U * st σ U) + V * st σ V := by sorry
