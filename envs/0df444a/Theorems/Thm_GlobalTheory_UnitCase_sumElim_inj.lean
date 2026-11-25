-- Prove2me | Theorems.Thm_GlobalTheory_UnitCase_sumElim_inj
-- name    : GlobalTheory.UnitCase.sumElim_inj
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:39:42.623029+00:00
-- url     : https://prove2.me/theorems/e757946e-626f-41bb-962d-fb48ad78ca29
-- title:
--   Unit Case: sum Elim inj
-- statement:
--   The Unit Case construction uses the sum Elim inj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LeWeightOfCoeffPow.lean#L192-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LeWeightOfCoeffPow.lean#L192-L195

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

theorem GlobalTheory.UnitCase.sumElim_inj {A B A' B' : κ →₀ ℕ} (h : Finsupp.sumElim A B = Finsupp.sumElim A' B') :
    A = A' ∧ B = B' := by sorry
