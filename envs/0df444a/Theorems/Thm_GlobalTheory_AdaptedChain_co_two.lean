-- Prove2me | Theorems.Thm_GlobalTheory_AdaptedChain_co_two
-- name    : GlobalTheory.AdaptedChain.co_two
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T00:24:45.656745+00:00
-- url     : https://prove2.me/theorems/4aa103a5-a6e7-4dc0-94fe-8800e7cbe2c9
-- title:
--   Adapted Chain: co two
-- statement:
--   The Adapted Chain construction uses the co two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/RowDataAdaptedChainData.lean#L571-L584
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/RowDataAdaptedChainData.lean#L571-L584

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

theorem GlobalTheory.AdaptedChain.co_two (S : Sys X) (h : I ⊕ J → C) (g lam : I → C)
    (e : ∀ k, (V.l : C) * h (Sum.inl k) = ∑ e, g e * S.tan e k + (V.l : C) * lam k) (b : I) :
    S.co h b = (V.l : C)⁻¹ * (g b + (V.l : C) * S.co (Sum.elim lam 0) b) := by sorry
