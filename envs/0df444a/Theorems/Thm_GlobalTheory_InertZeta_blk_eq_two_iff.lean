-- Prove2me | Theorems.Thm_GlobalTheory_InertZeta_blk_eq_two_iff
-- name    : GlobalTheory.InertZeta.blk_eq_two_iff
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T17:18:47.989804+00:00
-- url     : https://prove2.me/theorems/569e62d6-a93b-4a6f-aa23-ad03ffca5184
-- title:
--   Inert Zeta: blk eq two iff
-- statement:
--   The Inert Zeta construction uses the blk eq two iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnitaryIwasawaCellsDisjoint.lean#L19-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/UnitaryIwasawaCellsDisjoint.lean#L19-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_UnitaryLeviNormalizesUnipotentRadical
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnitaryIwasawaCellsDisjoint
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG GlobalTheory.SatakeWeyl
open GlobalTheory GlobalTheory.InertZeta
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}

theorem GlobalTheory.InertZeta.blk_eq_two_iff {l : Fin (N + 2)} : blk N l = 2 ↔ l = Fin.last (N + 1) := by sorry
