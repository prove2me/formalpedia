-- Prove2me | Theorems.Thm_GlobalTheory_InertZeta_HeisCoord_zero_ne_mid
-- name    : GlobalTheory.InertZeta.HeisCoord.zero_ne_mid
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T16:55:59.097869+00:00
-- url     : https://prove2.me/theorems/6698c982-1a98-4aa2-97c9-1738113d3bf9
-- title:
--   Heis Coord: zero ne mid
-- statement:
--   The Heis Coord construction uses the zero ne mid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnitaryHeisenbergRadicalCoordinates.lean#L57-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnitaryHeisenbergRadicalCoordinates.lean#L57-L57

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

theorem GlobalTheory.InertZeta.HeisCoord.zero_ne_mid (i : Fin N) : (0 : Fin (N + 2)) ≠ mid i := by sorry
