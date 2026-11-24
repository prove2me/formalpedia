-- Prove2me | Theorems.Thm_GlobalTheory_InertZeta_DualLat_IntT_mulVec
-- name    : GlobalTheory.InertZeta.DualLat.IntT.mulVec
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:51:28.528557+00:00
-- url     : https://prove2.me/theorems/5c75975d-8c1d-4015-82f7-3e28208d69ed
-- title:
--   Int T: mul Vec
-- statement:
--   The Int T construction uses the mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DualInterEqSum.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/DualInterEqSum.lean#L25-L29

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

theorem GlobalTheory.InertZeta.DualLat.IntT.mulVec {t : L} {M : Matrix (Fin N) (Fin N) L} {x : Fin N → L} (hM : IsInt M) (hx : IntT t x) :
    IntT t (M *ᵥ x) := by sorry
