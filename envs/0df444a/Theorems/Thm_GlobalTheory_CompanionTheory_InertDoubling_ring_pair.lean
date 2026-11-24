-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_InertDoubling_ring_pair
-- name    : GlobalTheory.CompanionTheory.InertDoubling.ring_pair
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:02:02.645593+00:00
-- url     : https://prove2.me/theorems/126a53c3-9316-425e-9d49-71046399ad9b
-- title:
--   Inert Doubling: ring pair
-- statement:
--   The Inert Doubling construction uses the ring pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CompletionExists.lean#L26-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/TwistedProofs/CompletionExists.lean#L26-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_TwistedProofs_CompletionExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.InertZeta GlobalTheory.Doubling GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.InertDoubling

theorem GlobalTheory.CompanionTheory.InertDoubling.ring_pair {R : Type} [Ring R] (J A B U V a b u v S : R) (hJ : J * J = 1)
    (h2 : a * u + b * v = 1) (h3 : a * J * A = b * J * B) :
    a * J * (J * u * J + A * S) - b * J * (-(J * v * J) + B * S) = J := by sorry
