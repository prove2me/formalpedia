-- Prove2me | Theorems.Thm_GlobalTheory_UnitCase_wilson_pow
-- name    : GlobalTheory.UnitCase.wilson_pow
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:36:47.239947+00:00
-- url     : https://prove2.me/theorems/ea75ab7d-2bc0-4fbf-ad7c-441c70412b95
-- title:
--   Unit Case: wilson pow
-- statement:
--   The Unit Case construction uses the wilson pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LeWeightOfCoeffPow.lean#L106-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LeWeightOfCoeffPow.lean#L106-L127

import Mathlib
import Definitions.Def_Formalism_DropLevelBounds_Statement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_WtAddSingle
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_LeWeightOfCoeffPow
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UnitaryBoundIntegral Formalism.IncomingBounds ReciprocityTheory.PGsh
open scoped BigOperators
noncomputable section
open GlobalTheory GlobalTheory.UnitCase
variable {C : Type} [Field C] {σ κ : Type}

theorem GlobalTheory.UnitCase.wilson_pow {l : ℕ} (hl : l.Prime) (b : ℕ) :
    ∃ w : ℤ, ((l * b).factorial : ℤ) = (-(l : ℤ)) ^ b * w ∧ (w : ZMod l) = (b.factorial : ZMod l) := by sorry
