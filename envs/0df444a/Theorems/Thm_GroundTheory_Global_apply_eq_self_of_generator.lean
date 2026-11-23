-- Prove2me | Theorems.Thm_GroundTheory_Global_apply_eq_self_of_generator
-- name    : GroundTheory.Global.apply_eq_self_of_generator
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:55:58.199678+00:00
-- url     : https://prove2.me/theorems/f9ea9a9a-2772-4ea1-a413-f1bc97080e11
-- title:
--   Global: apply eq self of generator
-- statement:
--   The Global construction uses the apply eq self of generator property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/CycTate.lean#L106-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/HerbrandQuotients/CycTate.lean#L106-L116

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_HerbrandAbstract
import Definitions.Def_GroundTheory_GlobalFields_HerbrandQuotients_CycTate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open GroundTheory.GroupCoh
variable {k G V : Type*} [CommRing k] [Group G] [AddCommGroup V] [Module k V]

theorem GroundTheory.Global.apply_eq_self_of_generator (ρ : Representation k G V) {σ : G}
    (hσ : ∀ g, g ∈ Subgroup.zpowers σ) {x : V} (hx : ρ σ x = x) (g : G) : ρ g x = x := by sorry
