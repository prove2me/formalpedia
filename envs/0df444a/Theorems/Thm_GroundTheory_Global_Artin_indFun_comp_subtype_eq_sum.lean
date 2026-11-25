-- Prove2me | Theorems.Thm_GroundTheory_Global_Artin_indFun_comp_subtype_eq_sum
-- name    : GroundTheory.Global.Artin.indFun_comp_subtype_eq_sum
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:13:32.513914+00:00
-- url     : https://prove2.me/theorems/66b95ec9-b4af-509a-8ed0-ba370ad654ec
-- title:
--   Artin: ind Fun comp subtype eq sum
-- statement:
--   The Artin construction uses the ind Fun comp subtype eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/Mackey.lean#L179-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/Mackey.lean#L179-L217

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_BrauerInductionInduced
import Definitions.Def_GroundTheory_TateCohomology_DoubleCosetSum
import Definitions.Def_GroundTheory_GlobalFields_Artin_Mackey
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open scoped Pointwise
open GroundTheory GroundTheory.Global GroundTheory.Global.Artin
open GroundTheory.LocalField
variable {G : Type*} [Group G]
variable [Fintype G]
open Classical

theorem GroundTheory.Global.Artin.indFun_comp_subtype_eq_sum (H D : Subgroup G) [Fintype H] [Fintype D] {f : H → ℂ}
    (hf : IsClassFun f) (x : DoubleCoset.Quotient (H : Set G) D → G)
    (hx : ∀ q, DoubleCoset.mk H D (x q) = q) :
    indFun H.subtype f ∘ D.subtype =
      ∑ q, indFun ((MulAut.conj (x q)⁻¹ • H : Subgroup G).subgroupOf D).subtype
        (conjFun H D (x q) f) := by sorry
