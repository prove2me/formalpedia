-- Prove2me | Theorems.Thm_GlobalTheory_InertZeta_HeisCoord_mem_radQ_of_shape
-- name    : GlobalTheory.InertZeta.HeisCoord.mem_radQ_of_shape
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:22:28.377796+00:00
-- url     : https://prove2.me/theorems/1ccd129c-f127-4383-81ed-5874a37b726a
-- title:
--   Heis Coord: mem rad Q of shape
-- statement:
--   The Heis Coord construction uses the mem rad Q of shape property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnitaryHeisenbergRadicalCoordinates.lean#L96-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnitaryHeisenbergRadicalCoordinates.lean#L96-L102

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryHeisenbergRadicalCoordinates
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.UG Matrix GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.InertZeta GlobalTheory.InertZeta.HeisCoord
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}

theorem GlobalTheory.InertZeta.HeisCoord.mem_radQ_of_shape {u : GU σ (N + 2)} {r b : Fin N → L} {c : L} (h : Shape (mat u) r b c) :
    u ∈ radQ σ N := by sorry
