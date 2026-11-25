-- Prove2me | Theorems.Thm_GlobalTheory_UnitCase_not_dvd_mfact
-- name    : GlobalTheory.UnitCase.not_dvd_mfact
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:39:55.681964+00:00
-- url     : https://prove2.me/theorems/0eb489eb-1efa-4ee4-bb16-76e3c8f0de45
-- title:
--   Unit Case: not dvd mfact
-- statement:
--   The Unit Case construction uses the not dvd mfact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LeWeightOfCoeffPow.lean#L154-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/LeWeightOfCoeffPow.lean#L154-L158

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

theorem GlobalTheory.UnitCase.not_dvd_mfact [Fintype κ] {l : ℕ} (hl : l.Prime) (β : κ →₀ ℕ) (h : ∀ j, β j < l) :
    ¬ l ∣ mfact β := by sorry
