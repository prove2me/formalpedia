-- Prove2me | Theorems.Thm_GlobalTheory_AdaptedChain_elim_frob
-- name    : GlobalTheory.AdaptedChain.elim_frob
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:24:41.238844+00:00
-- url     : https://prove2.me/theorems/a08da235-7353-4dee-a481-74b57834c6ac
-- title:
--   Adapted Chain: elim frob
-- statement:
--   The Adapted Chain construction uses the elim frob property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/RowDataAdaptedChainData.lean#L166-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/RowDataAdaptedChainData.lean#L166-L177

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

theorem GlobalTheory.AdaptedChain.elim_frob [IsAlgClosed C] {M : Type} (Q : Finset I) (w : I → M → C)
    (hw : ∀ x e, V.Ge 0 (w x e)) (E : Finset M) (k : ℕ) :
    ∃ (P : Matrix I I C) (Q' : Finset I), admitted V Q P ∧ Q' ⊆ Q ∧
    Q.card ≤ Q'.card + E.card ∧ ∀ c ∈ Q', ∀ e ∈ E, V.Ge 1 (∑ x, P c x ^ (V.l ^ k) * w x e) := by sorry
