-- Prove2me | Theorems.Thm_GlobalTheory_AdaptedChain_stepB
-- name    : GlobalTheory.AdaptedChain.stepB
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:24:37.704272+00:00
-- url     : https://prove2.me/theorems/5b0f50ba-5e33-4f0a-918c-bd8d27ac0113
-- title:
--   Adapted Chain: step B
-- statement:
--   The Adapted Chain construction uses the step B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/RowDataAdaptedChainData.lean#L312-L381
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/RowDataAdaptedChainData.lean#L312-L381

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

theorem GlobalTheory.AdaptedChain.stepB [IsAlgClosed C] (S : Sys X) (b : ZMod d) (Q : Finset I) (hQ : ∀ c ∈ Q, X.ty (Sum.inl c) = b)
    (L : AddSubgroup (I → C)) (hL : Stable V L) (hQL : ∀ c ∈ Q, S.tan c ∈ L)
    (hG : ∀ c ∈ Q, ∀ k, S.cur c 1 (Sum.inl k) = 0) (E : Finset I) :
    ∃ (S' : Sys X) (Q' : Finset I), Q' ⊆ Q ∧ Q.card ≤ Q'.card + E.card ∧
      (∀ c, c ∉ Q → S'.cur c = S.cur c) ∧ (∀ c ∈ Q, S'.tan c ∈ L) ∧
      (∀ c ∈ Q, ∀ k, S'.cur c 1 (Sum.inl k) = 0) ∧
      ∀ c ∈ Q', ∃ g lam : I → C, (∀ e, V.Ge 0 (g e)) ∧ (∀ e, V.Ge 0 (lam e)) ∧
        (∀ e, g e ≠ 0 → X.ty (Sum.inl e) = b + 2 ∧ e ∉ E) ∧
        ∀ k, (V.l : C) * S'.cur c 2 (Sum.inl k) = ∑ e, g e * S.tan e k + (V.l : C) * lam k := by sorry
