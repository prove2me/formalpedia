-- Prove2me | Theorems.Thm_GroundTheory_Global_Artin_indFun_subtype_apply
-- name    : GroundTheory.Global.Artin.indFun_subtype_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:45:48.8015+00:00
-- url     : https://prove2.me/theorems/061e181c-1f29-5f88-8489-a95589d3ac73
-- title:
--   Artin: ind Fun subtype apply
-- statement:
--   The Artin construction uses the ind Fun subtype apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/Mackey.lean#L57-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/Mackey.lean#L57-L75

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

theorem GroundTheory.Global.Artin.indFun_subtype_apply [Fintype G] (H : Subgroup G) [Fintype H] (f : H → ℂ) (s : G) :
    indFun H.subtype f s = (Nat.card H : ℂ)⁻¹ * ∑ t : G, extendByZero H f (t⁻¹ * s * t) := by sorry
