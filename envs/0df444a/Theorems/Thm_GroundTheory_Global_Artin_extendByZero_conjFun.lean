-- Prove2me | Theorems.Thm_GroundTheory_Global_Artin_extendByZero_conjFun
-- name    : GroundTheory.Global.Artin.extendByZero_conjFun
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T01:45:43.697242+00:00
-- url     : https://prove2.me/theorems/eb6147d5-f36f-5cf3-84c3-70f98cd84755
-- title:
--   Artin: extend By Zero conj Fun
-- statement:
--   The Artin construction uses the extend By Zero conj Fun property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/Mackey.lean#L165-L173
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/Mackey.lean#L165-L173

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

theorem GroundTheory.Global.Artin.extendByZero_conjFun (H D : Subgroup G) (x : G) (f : H → ℂ) (y : D) :
    extendByZero _ (conjFun H D x f) y = extendByZero H f (x * y * x⁻¹) := by sorry
