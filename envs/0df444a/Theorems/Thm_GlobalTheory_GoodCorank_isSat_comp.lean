-- Prove2me | Theorems.Thm_GlobalTheory_GoodCorank_isSat_comp
-- name    : GlobalTheory.GoodCorank.isSat_comp
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:33:43.656716+00:00
-- url     : https://prove2.me/theorems/da2a892d-0883-430b-8da7-09ef7f8ff033
-- title:
--   Good Corank: is Sat comp
-- statement:
--   The Good Corank construction uses the is Sat comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsSaturatedGoodVectorsSmallCorank.lean#L57-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsSaturatedGoodVectorsSmallCorank.lean#L57-L70

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_Interface
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_RowDataAdaptedChainData
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_ExistsSaturatedGoodVectorsSmallCorank
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism.L2.FormalSeriesBounds
open GlobalTheory GlobalTheory.GoodCorank
variable {C : Type} [Field C] {V : VF C}

theorem GlobalTheory.GoodCorank.isSat_comp {M N : ℕ} {σ : Type} [Fintype σ] {A : Fin M → Fin N → C} {w : Fin N → σ → C}
    (hA : IsSat V A) (hw : IsSat V w) : IsSat V (fun ν c => ∑ k, A ν k * w k c) := by sorry
