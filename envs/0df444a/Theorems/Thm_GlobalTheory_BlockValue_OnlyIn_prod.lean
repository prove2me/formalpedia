-- Prove2me | Theorems.Thm_GlobalTheory_BlockValue_OnlyIn_prod
-- name    : GlobalTheory.BlockValue.OnlyIn.prod
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T00:50:32.151329+00:00
-- url     : https://prove2.me/theorems/bf768595-c69f-4bd9-8534-df8916cf275e
-- title:
--   Only In: prod
-- statement:
--   The Only In construction uses the prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/BlockValueOnRowsEq.lean#L47-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/BlockValueOnRowsEq.lean#L47-L49

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

theorem GlobalTheory.BlockValue.OnlyIn.prod {S : σ → Prop} {ι : Type} (s : Finset ι) {f : ι → MvPowerSeries σ C}
    (hf : ∀ i ∈ s, OnlyIn S (f i)) : OnlyIn S (∏ i ∈ s, f i) := by sorry
