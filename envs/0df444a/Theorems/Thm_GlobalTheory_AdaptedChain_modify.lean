-- Prove2me | Theorems.Thm_GlobalTheory_AdaptedChain_modify
-- name    : GlobalTheory.AdaptedChain.modify
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:24:53.164904+00:00
-- url     : https://prove2.me/theorems/55ea6655-4624-4105-b09a-778e83f815f6
-- title:
--   Adapted Chain: modify
-- statement:
--   The Adapted Chain construction uses the modify property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/RowDataAdaptedChainData.lean#L262-L285
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/RowDataAdaptedChainData.lean#L262-L285

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

theorem GlobalTheory.AdaptedChain.modify (S : Sys X) (Q : Finset I) (h : ∀ c ∈ Q, ∀ k, V.Ge 0 (S.cur c 1 (Sum.inl k))) :
    ∃ S' : Sys X, (∀ c, c ∉ Q → S'.cur c = S.cur c) ∧ S'.tan = S.tan ∧
      ∀ c ∈ Q, ∀ k, S'.cur c 1 (Sum.inl k) = 0 := by sorry
