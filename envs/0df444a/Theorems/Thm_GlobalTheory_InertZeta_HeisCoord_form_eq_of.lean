-- Prove2me | Theorems.Thm_GlobalTheory_InertZeta_HeisCoord_form_eq_of
-- name    : GlobalTheory.InertZeta.HeisCoord.form_eq_of
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T17:17:44.099291+00:00
-- url     : https://prove2.me/theorems/7d0d41b9-5142-4657-ad74-711d020c4cbf
-- title:
--   Heis Coord: form eq of
-- statement:
--   The Heis Coord construction uses the form eq of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnitaryHeisenbergRadicalCoordinates.lean#L60-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnitaryHeisenbergRadicalCoordinates.lean#L60-L76

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

theorem GlobalTheory.InertZeta.HeisCoord.form_eq_of (hσσ : ∀ x, σ (σ x) = x) {M : Matrix (Fin (N + 2)) (Fin (N + 2)) L} {r b : Fin N → L} {c : L}
    (h : Shape M r b c) (h1 : ∀ j, b j.rev + σ (r j) = 0) (h2 : c + ∑ k, σ (b k.rev) * b k + σ c = 0) :
    cT σ M * antiJ L (N + 2) * M = antiJ L (N + 2) := by sorry
