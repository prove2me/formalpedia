-- Prove2me | Theorems.Thm_GlobalTheory_InertZeta_det_mat_ne_zero
-- name    : GlobalTheory.InertZeta.det_mat_ne_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:45:52.331797+00:00
-- url     : https://prove2.me/theorems/e3a09d93-83ee-4c8b-be1b-6a64fd6effb9
-- title:
--   Inert Zeta: det mat ne zero
-- statement:
--   The Inert Zeta construction uses the det mat ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasSumSpherical.lean#L13-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/HasSumSpherical.lean#L13-L13

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasSumSpherical
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
open GlobalTheory GlobalTheory.InertZeta
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {ϖ : L} {q N : ℕ}
omit [Valued L (WithZero (Multiplicative ℤ))]

theorem GlobalTheory.InertZeta.det_mat_ne_zero {n : ℕ} (g : GU σ n) : (mat g).det ≠ 0 := by sorry
