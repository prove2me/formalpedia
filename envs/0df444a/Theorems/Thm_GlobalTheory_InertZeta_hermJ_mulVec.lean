-- Prove2me | Theorems.Thm_GlobalTheory_InertZeta_hermJ_mulVec
-- name    : GlobalTheory.InertZeta.hermJ_mulVec
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:19:05.043886+00:00
-- url     : https://prove2.me/theorems/e777fa50-d501-4d72-86f6-0ded6f2f5f75
-- title:
--   Inert Zeta: herm J mul Vec
-- statement:
--   The Inert Zeta construction uses the herm J mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SmallCornerOfHeisenbergDuality.lean#L43-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/SmallCornerOfHeisenbergDuality.lean#L43-L63

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

theorem GlobalTheory.InertZeta.hermJ_mulVec (g : GU σ N) (x y : Fin N → L) :
    hermJ σ (mat g *ᵥ x) (mat g *ᵥ y) = hermJ σ x y := by sorry
