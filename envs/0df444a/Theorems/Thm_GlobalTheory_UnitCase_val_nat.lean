-- Prove2me | Theorems.Thm_GlobalTheory_UnitCase_val_nat
-- name    : GlobalTheory.UnitCase.val_nat
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:36:39.411861+00:00
-- url     : https://prove2.me/theorems/35d22e97-98d2-4246-85c0-dc110ad541de
-- title:
--   Unit Case: val nat
-- statement:
--   The Unit Case construction uses the val nat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LeWeightOfCoeffPow.lean#L522-L529
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LeWeightOfCoeffPow.lean#L522-L529

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

theorem GlobalTheory.UnitCase.val_nat {v : AddValuation C (WithTop ℝ)} {l : ℕ}
    (hp : ∀ p : ℕ, p.Prime → p ≠ l → v (p : C) = 0) (n : ℕ) (hn : ¬ l ∣ n) : v (n : C) = 0 := by sorry
