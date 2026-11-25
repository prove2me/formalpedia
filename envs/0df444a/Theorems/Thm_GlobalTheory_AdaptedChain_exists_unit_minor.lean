-- Prove2me | Theorems.Thm_GlobalTheory_AdaptedChain_exists_unit_minor
-- name    : GlobalTheory.AdaptedChain.exists_unit_minor
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:24:43.620025+00:00
-- url     : https://prove2.me/theorems/4f26593e-8b3b-44e6-a243-65d238635803
-- title:
--   Adapted Chain: exists unit minor
-- statement:
--   The Adapted Chain construction uses the exists unit minor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/RowDataAdaptedChainData.lean#L179-L207
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/RowDataAdaptedChainData.lean#L179-L207

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_RowDataAdaptedChainData
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
open Classical
open Formalism.L2.FormalSeriesBounds
open GlobalTheory GlobalTheory.AdaptedChain
variable {C : Type} [Field C] {V : VF C} {d : ℕ} {I J : Type} [Fintype I] [Fintype J]

theorem GlobalTheory.AdaptedChain.exists_unit_minor {ι : Type} [Fintype ι] (U : ι → I → C) (w : I → ι → C)
    (hU : ∀ c x, V.Ge 0 (U c x)) (hw : ∀ x c, V.Ge 0 (w x c))
    (h : ∀ c c', ∑ x, U c x * w x c' = if c = c' then 1 else 0) :
    ∃ f : ι → I, V.v (Matrix.of fun c' c => U c (f c')).det = 0 := by sorry
