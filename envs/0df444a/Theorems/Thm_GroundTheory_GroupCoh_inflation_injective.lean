-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_inflation_injective
-- name    : GroundTheory.GroupCoh.inflation_injective
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:43:19.139942+00:00
-- url     : https://prove2.me/theorems/5534fd6a-01fb-484f-95f8-b08846ab5904
-- title:
--   Group Coh: inflation injective
-- statement:
--   The Group Coh construction uses the inflation injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/InfRes.lean#L159-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/InfRes.lean#L159-L163

import Mathlib
import Definitions.Def_GroundTheory_TateCohomology_DeltaMap
import Definitions.Def_GroundTheory_TateCohomology_CoindOne
import Definitions.Def_GroundTheory_TateCohomology_InfRes
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
open CategoryTheory Limits groupCohomology Rep
universe u
variable {k G : Type u} [CommRing k] [Group G]
variable (A : Rep k G) (S : Subgroup G) [S.Normal]
variable {A S}

theorem GroundTheory.GroupCoh.inflation_injective {q : ℕ} (hq : q ≠ 0)
    (hA : ∀ i, 0 < i → i < q → IsZero (groupCohomology (res S.subtype A) i)) :
    Function.Injective (inflation A S q).hom := by sorry
