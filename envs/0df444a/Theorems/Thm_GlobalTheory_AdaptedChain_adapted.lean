-- Prove2me | Theorems.Thm_GlobalTheory_AdaptedChain_adapted
-- name    : GlobalTheory.AdaptedChain.adapted
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:25:29.193687+00:00
-- url     : https://prove2.me/theorems/0e024ba0-1b60-431a-9835-2b47c005d226
-- title:
--   Adapted Chain: adapted
-- statement:
--   The Adapted Chain construction uses the adapted property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/RowDataAdaptedChainData.lean#L500-L557
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/RowDataAdaptedChainData.lean#L500-L557

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CartesianBoundOnCurves
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_CoeffIterateZero
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_ScaledSecondIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_RowDataAdaptedChainData
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

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
variable {X : Cart V d I J}

theorem GlobalTheory.AdaptedChain.adapted (X : Cart V d I J) {ι : Type} [Fintype ι] (U : ι → I → C) (w : I → ι → C)
    (hU : ∀ c x, V.Ge 0 (U c x)) (hw : ∀ x c, V.Ge 0 (w x c))
    (h : ∀ c c', ∑ x, U c x * w x c' = if c = c' then 1 else 0) (a : ZMod d)
    (ha : ∀ c x, X.ty (Sum.inl x) ≠ a → U c x = 0) :
    ∃ (S : Sys X) (Q : Finset I), (∀ c ∈ Q, X.ty (Sum.inl c) = a) ∧ Q.card = Fintype.card ι ∧
      ∀ c ∈ Q, S.tan c ∈ intSpan V U := by sorry
