-- Prove2me | Theorems.Thm_GlobalTheory_InertZeta_HeisCoord_antiJ_eq
-- name    : GlobalTheory.InertZeta.HeisCoord.antiJ_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T16:55:48.877812+00:00
-- url     : https://prove2.me/theorems/e289b267-5205-4b50-8288-b5c1c957d6fa
-- title:
--   Heis Coord: anti J eq
-- statement:
--   The Heis Coord construction uses the anti J eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnitaryHeisenbergRadicalCoordinates.lean#L24-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnitaryHeisenbergRadicalCoordinates.lean#L24-L25

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
omit [Valued L (WithZero (Multiplicative ℤ))]

theorem GlobalTheory.InertZeta.HeisCoord.antiJ_eq {n : ℕ} (a b : Fin n) : antiJ L n a b = if a = b.rev then 1 else 0 := by sorry
