-- Prove2me | Theorems.Thm_GroundTheory_GroupCoh_infResShortComplex_mono_exact
-- name    : GroundTheory.GroupCoh.infResShortComplex_mono_exact
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:58:58.445619+00:00
-- url     : https://prove2.me/theorems/d0c342f3-d89d-4d9c-bc75-0a6841d49e4b
-- title:
--   Group Coh: inf Res Short Complex mono exact
-- statement:
--   The Group Coh construction uses the inf Res Short Complex mono exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/InfRes.lean#L150-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/TateCohomology/InfRes.lean#L150-L155

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

theorem GroundTheory.GroupCoh.infResShortComplex_mono_exact (n : ℕ) :
    ∀ A : Rep k G, (∀ i, 0 < i → i < n + 1 → IsZero (groupCohomology (res S.subtype A) i)) →
      Mono (infResShortComplex A S n).f ∧ (infResShortComplex A S n).Exact := by sorry
