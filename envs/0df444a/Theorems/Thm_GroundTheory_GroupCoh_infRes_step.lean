-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_infRes_step
-- name    : GroundTheory.GroupCoh.infRes_step
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:43:42.143798+00:00
-- url     : https://prove2.me/theorems/83c9f2af-b0f5-411a-939e-c4e6f0cf6ea3
-- title:
--   Group Coh: inf Res step
-- statement:
--   The Group Coh construction uses the inf Res step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/InfRes.lean#L106-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/InfRes.lean#L106-L148

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

theorem GroundTheory.GroupCoh.infRes_step (n : ℕ)
    (ih : ∀ B : Rep k G, (∀ i, 0 < i → i < n + 1 → IsZero (groupCohomology (res S.subtype B) i)) →
      Mono (infResShortComplex B S n).f ∧ (infResShortComplex B S n).Exact)
    (hA : ∀ i, 0 < i → i < n + 2 → IsZero (groupCohomology (res S.subtype A) i)) :
    Mono (infResShortComplex A S (n + 1)).f ∧ (infResShortComplex A S (n + 1)).Exact := by sorry
