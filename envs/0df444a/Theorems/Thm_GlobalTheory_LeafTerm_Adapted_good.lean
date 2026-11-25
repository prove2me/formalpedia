-- Prove2me | Theorems.Thm_GlobalTheory_LeafTerm_Adapted_good
-- name    : GlobalTheory.LeafTerm.Adapted.good
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:25:53.406211+00:00
-- url     : https://prove2.me/theorems/14b6ec0d-aee5-4528-9d64-87f37ac5cfa5
-- title:
--   Adapted: good
-- statement:
--   The Adapted construction uses the good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GoodOfMemSlots.lean#L61-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GoodOfMemSlots.lean#L61-L65

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_LatticeInclusionFormsInjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnramifiedDepth_GoodOfMemSlots
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
open GlobalTheory GlobalTheory.LeafTerm
variable {C : Type} [Field C]
variable {Z I J : Type} [Fintype I]
variable [Fintype J] {V : VF C} {d : ℕ} {X : Cart V d I J}
variable {S : Sys X} {D : Formalism.BaseCaseIdentities.Data C Z I} {a : ZMod d} {i : ℕ}

theorem GlobalTheory.LeafTerm.Adapted.good (h : Adapted S D a i) {c : I} (hc : D.good c) :
    X.Good (X.ty (Sum.inl c)) (S.tan c) (S.cur c) := by sorry
