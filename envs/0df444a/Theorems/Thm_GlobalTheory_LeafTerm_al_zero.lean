-- Prove2me | Theorems.Thm_GlobalTheory_LeafTerm_al_zero
-- name    : GlobalTheory.LeafTerm.al_zero
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T00:25:32.380617+00:00
-- url     : https://prove2.me/theorems/c0fba1c4-f47c-4d5f-b73b-4e0304b33a89
-- title:
--   Leaf Term: al zero
-- statement:
--   The Leaf Term construction uses the al zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GoodOfMemSlots.lean#L52-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/GoodOfMemSlots.lean#L52-L53

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

theorem GlobalTheory.LeafTerm.al_zero (S : Sys X) (c x : I) : S.al c 0 x = S.tan c x := by sorry
