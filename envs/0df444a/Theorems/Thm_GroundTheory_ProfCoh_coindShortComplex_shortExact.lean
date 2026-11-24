-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_coindShortComplex_shortExact
-- name    : GroundTheory.ProfCoh.coindShortComplex_shortExact
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T16:05:21.666801+00:00
-- url     : https://prove2.me/theorems/b539e4bd-72b6-4801-8331-529f4be07c59
-- title:
--   Prof Coh: coind Short Complex short Exact
-- statement:
--   The Prof Coh construction uses the coind Short Complex short Exact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CoinducedModules.lean#L155-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CoinducedModules.lean#L155-L167

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_DiscreteModules_IsDiscreteRepIffForallExistsOpenNormalSubgroup
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules
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
open CategoryTheory Filter Topology
universe u
variable (k G : Type u) [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (X : Type u) [AddCommGroup X] [Module k X]
variable {k G}

theorem GroundTheory.ProfCoh.coindShortComplex_shortExact (A : Rep.{u} k G) [IsDiscreteRep A] :
    (coindShortComplex A).ShortExact := by sorry
