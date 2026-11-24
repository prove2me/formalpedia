-- Prove2me | Theorems.Thm_GlobalTheory_InertZeta_DualLat_IntT_sub
-- name    : GlobalTheory.InertZeta.DualLat.IntT.sub
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T17:17:43.933863+00:00
-- url     : https://prove2.me/theorems/f2a379f3-077a-4cfb-817c-da0e5f5178a8
-- title:
--   Int T: sub
-- statement:
--   The Int T construction uses the sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DualInterEqSum.lean#L22-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DualInterEqSum.lean#L22-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_DualInterEqSum
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
open GlobalTheory GlobalTheory.InertZeta GlobalTheory.InertZeta.DualLat
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {N : ℕ}

theorem GlobalTheory.InertZeta.DualLat.IntT.sub {t : L} {x y : Fin N → L} (hx : IntT t x) (hy : IntT t y) : IntT t (x - y) := by sorry
