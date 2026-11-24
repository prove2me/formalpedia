-- Prove2me | Theorems.Thm_GlobalTheory_InertZeta_HeisCoord_form_last_last
-- name    : GlobalTheory.InertZeta.HeisCoord.form_last_last
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:22:08.004351+00:00
-- url     : https://prove2.me/theorems/5c3471d4-bf40-4855-88fa-7c5b02799242
-- title:
--   Heis Coord: form last last
-- statement:
--   The Heis Coord construction uses the form last last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnitaryHeisenbergRadicalCoordinates.lean#L51-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnitaryHeisenbergRadicalCoordinates.lean#L51-L55

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

theorem GlobalTheory.InertZeta.HeisCoord.form_last_last {M : Matrix (Fin (N + 2)) (Fin (N + 2)) L} {r b : Fin N → L} {c : L} (h : Shape M r b c) :
    (cT σ M * antiJ L (N + 2) * M) (Fin.last (N + 1)) (Fin.last (N + 1)) = c + ∑ k, σ (b k.rev) * b k + σ c := by sorry
