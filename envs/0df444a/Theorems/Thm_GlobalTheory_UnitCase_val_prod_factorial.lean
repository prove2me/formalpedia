-- Prove2me | Theorems.Thm_GlobalTheory_UnitCase_val_prod_factorial
-- name    : GlobalTheory.UnitCase.val_prod_factorial
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T00:41:12.815848+00:00
-- url     : https://prove2.me/theorems/8e249568-58ee-4826-8c51-4c21e5acb818
-- title:
--   Unit Case: val prod factorial
-- statement:
--   The Unit Case construction uses the val prod factorial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LeWeightOfCoeffPow.lean#L539-L546
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LeWeightOfCoeffPow.lean#L539-L546

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

theorem GlobalTheory.UnitCase.val_prod_factorial {v : AddValuation C (WithTop ℝ)} {l : ℕ} (hl : l.Prime)
    (hp : ∀ p : ℕ, p.Prime → p ≠ l → v (p : C) = 0) (s : Finset ℕ) (f : ℕ → ℕ)
    (hf : ∀ c ∈ s, f c < l) : v (∏ c ∈ s, ((f c).factorial : C)) = 0 := by sorry
