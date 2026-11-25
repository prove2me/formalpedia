-- Prove2me | Theorems.Thm_GroundTheory_Global_Artin_extendByZero_conj
-- name    : GroundTheory.Global.Artin.extendByZero_conj
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T03:13:55.957442+00:00
-- url     : https://prove2.me/theorems/1eb8ba33-73a2-44fc-bc6a-91b510d9daa3
-- title:
--   Artin: extend By Zero conj
-- statement:
--   The Artin construction uses the extend By Zero conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/Mackey.lean#L46-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/Mackey.lean#L46-L55

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

theorem GroundTheory.Global.Artin.extendByZero_conj {H : Subgroup G} {f : H → ℂ} (hf : IsClassFun f) {h : G} (hh : h ∈ H)
    (g : G) : extendByZero H f (h * g * h⁻¹) = extendByZero H f g := by sorry
