-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_sum_coindBotProj
-- name    : GroundTheory.GroupCoh.sum_coindBotProj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:02:49.98572+00:00
-- url     : https://prove2.me/theorems/d1605a26-3592-470a-bdd3-f33ab0d6b248
-- title:
--   Group Coh: sum coind Bot Proj
-- statement:
--   The Group Coh construction uses the sum coind Bot Proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/Induced.lean#L105-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/Induced.lean#L105-L116

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_Induced
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.GroupCoh
open CategoryTheory Limits groupCohomology groupHomology Rep
universe u
variable {k G : Type u} [CommRing k] [Group G] [Fintype G]
variable (B : Rep.{u} k (⊥ : Subgroup G))
open scoped Classical

theorem GroundTheory.GroupCoh.sum_coindBotProj (f : coind (⊥ : Subgroup G).subtype B) :
    ∑ g : G, (coind (⊥ : Subgroup G).subtype B).ρ g
      (coindBotProj B ((coind (⊥ : Subgroup G).subtype B).ρ g⁻¹ f)) = f := by sorry
