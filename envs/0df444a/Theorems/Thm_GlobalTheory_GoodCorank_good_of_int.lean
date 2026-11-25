-- Prove2me | Theorems.Thm_GlobalTheory_GoodCorank_good_of_int
-- name    : GlobalTheory.GoodCorank.good_of_int
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:33:27.847933+00:00
-- url     : https://prove2.me/theorems/dd2ddf87-0cb8-473c-9e2c-fcaab349b0d0
-- title:
--   Good Corank: good of int
-- statement:
--   The Good Corank construction uses the good of int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsSaturatedGoodVectorsSmallCorank.lean#L105-L118
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnramifiedDepth/ExistsSaturatedGoodVectorsSmallCorank.lean#L105-L118

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
variable {d : ℕ} {I J : Type} [Fintype I] [DecidableEq I]

theorem GlobalTheory.GoodCorank.good_of_int (G : Cart V d I J) {a : ZMod d} {u : I → C} {y : ℕ → I ⊕ J → C} (hy : G.IsCurve a u y)
    (h1 : ∀ b, V.Ge 0 (y 1 (Sum.inl b))) : ∃ x, G.Good a u x := by sorry
