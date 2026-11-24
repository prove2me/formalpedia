-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertDual_iff_of_inverse
-- name    : GlobalTheory.CompanionTheory.InertDual.iff_of_inverse
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:02:17.783447+00:00
-- url     : https://prove2.me/theorems/611b301f-af85-4e48-a63e-3e909b460aa3
-- title:
--   Inert Dual: iff of inverse
-- statement:
--   The Inert Dual construction uses the iff of inverse property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/DualPairingExists.lean#L56-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/DualPairingExists.lean#L56-L72

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_DualPairingExists
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertDual
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {N : ℕ}

theorem GlobalTheory.CompanionTheory.InertDual.iff_of_inverse {D E Q R Dg : Matrix (Fin N) (Fin N) L} (hED : E * D = 1) (hQ : IsInt (Q * E))
    (hR : IsInt (R * E)) (hDg : IsInt Dg) (hD : IsInt D) (e : D = Dg * R + D * Q) (B : Fin N → L) :
    (∀ i, (D *ᵥ B) i ∈ intL L) ↔ (∀ i, (Q *ᵥ B) i ∈ intL L) ∧ ∀ i, (R *ᵥ B) i ∈ intL L := by sorry
