-- Prove2me | Theorems.Thm_GlobalTheory_InertZeta_hermJ_int
-- name    : GlobalTheory.InertZeta.hermJ_int
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:19:34.305843+00:00
-- url     : https://prove2.me/theorems/cd35f147-5eb1-49ae-9800-e6fdbd6fcb23
-- title:
--   Inert Zeta: herm J int
-- statement:
--   The Inert Zeta construction uses the herm J int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SmallCornerOfHeisenbergDuality.lean#L70-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SmallCornerOfHeisenbergDuality.lean#L70-L76

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_HasLenOfLatLen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_AntiJMulApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_SmallCornerOfHeisenbergDuality
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
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {σ : L →+* L} {N : ℕ}

theorem GlobalTheory.InertZeta.hermJ_int {ϖ : L} (hσ : ∀ x, Valued.v (σ x) = Valued.v x) (hϖ : σ ϖ = ϖ) (e : ℕ) (x : Fin N → L)
    (h : ∀ i, ϖ ^ e * x i ∈ intL L) : ϖ ^ (2 * e) * hermJ σ x x ∈ intL L := by sorry
