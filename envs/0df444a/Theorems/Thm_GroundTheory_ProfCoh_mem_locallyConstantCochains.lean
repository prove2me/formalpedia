-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_mem_locallyConstantCochains
-- name    : GroundTheory.ProfCoh.mem_locallyConstantCochains
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T16:03:42.305331+00:00
-- url     : https://prove2.me/theorems/d0a39b90-0c68-4a9f-963a-3ff1ca389743
-- title:
--   Prof Coh: mem locally Constant Cochains
-- statement:
--   The Prof Coh construction uses the mem locally Constant Cochains property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/ContinuousCochains.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/ContinuousCochains.lean#L19-L21

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_DiscreteModules_IsDiscreteRepIffForallExistsOpenNormalSubgroup
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.ProfCoh
open CategoryTheory groupCohomology
universe u
variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G]

theorem GroundTheory.ProfCoh.mem_locallyConstantCochains (A : Rep.{u} k G) {n : ℕ} (f : (Fin n → G) → A) :
    f ∈ locallyConstantCochains A n ↔ IsLocallyConstant f := by sorry
