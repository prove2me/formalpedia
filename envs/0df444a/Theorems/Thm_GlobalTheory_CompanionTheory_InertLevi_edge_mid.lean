-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertLevi_edge_mid
-- name    : GlobalTheory.CompanionTheory.InertLevi.edge_mid
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:47:41.298529+00:00
-- url     : https://prove2.me/theorems/fd981dd3-2338-4ba4-9307-d858930aebab
-- title:
--   Inert Levi: edge mid
-- statement:
--   The Inert Levi construction uses the edge mid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/LeviDecompositionExists.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/LeviDecompositionExists.lean#L18-L19

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_LeviDecompositionExists
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertLevi
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}
omit [Valued L (WithZero (Multiplicative ℤ))]

theorem GlobalTheory.CompanionTheory.InertLevi.edge_mid (c d : L) (f : Fin N → L) (j : Fin N) : edge c d f (mid j) = f j := by sorry
