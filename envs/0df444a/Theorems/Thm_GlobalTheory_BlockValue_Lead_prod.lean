-- Prove2me | Theorems.Thm_GlobalTheory_BlockValue_Lead_prod
-- name    : GlobalTheory.BlockValue.Lead.prod
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:50:14.467994+00:00
-- url     : https://prove2.me/theorems/729f82e1-55d2-4bb0-b60b-818eb687930f
-- title:
--   Lead: prod
-- statement:
--   The Lead construction uses the prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/BlockValueOnRowsEq.lean#L110-L119
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/BlockValueOnRowsEq.lean#L110-L119

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BiadditiveInSingleVariables
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_DetPowDiagonalRowsBlockJetRestrict
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_BlockValueOnRowsEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.UnitaryBoundIntegral
open scoped BigOperators
open GlobalTheory GlobalTheory.BlockValue
variable {C : Type} [Field C] {σ κ : Type}

theorem GlobalTheory.BlockValue.Lead.prod {π : σ → κ} {ι : Type} (s : Finset ι) {d : ι → σ →₀ ℕ}
    {f : ι → MvPowerSeries σ C} (hf : ∀ i ∈ s, Lead π (d i) (f i)) :
    Lead π (∑ i ∈ s, d i) (∏ i ∈ s, f i) := by sorry
