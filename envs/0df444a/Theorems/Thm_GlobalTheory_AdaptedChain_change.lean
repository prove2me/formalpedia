-- Prove2me | Theorems.Thm_GlobalTheory_AdaptedChain_change
-- name    : GlobalTheory.AdaptedChain.change
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:24:46.019425+00:00
-- url     : https://prove2.me/theorems/529956d0-226b-4d1c-8abb-d178a37d15b9
-- title:
--   Adapted Chain: change
-- statement:
--   The Adapted Chain construction uses the change property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/RowDataAdaptedChainData.lean#L219-L260
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/RowDataAdaptedChainData.lean#L219-L260

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

theorem GlobalTheory.AdaptedChain.change (S : Sys X) (b : ZMod d) (Q : Finset I) (hQ : ∀ c ∈ Q, X.ty (Sum.inl c) = b)
    (L : AddSubgroup (I → C)) (hL : Stable V L) (hQL : ∀ c ∈ Q, S.tan c ∈ L)
    (P : Matrix I I C) (hP : admitted V Q P) :
    ∃ S' : Sys X, (∀ c, c ∉ Q → S'.cur c = S.cur c) ∧ (∀ c ∈ Q, S'.tan c ∈ L) ∧
      ∀ c i n, S'.cur c i n = ∑ x, P c x ^ (V.l ^ i) * S.cur x i n := by sorry
