-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_coindHomotopy_identity
-- name    : GroundTheory.ProfCoh.coindHomotopy_identity
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:49:05.368471+00:00
-- url     : https://prove2.me/theorems/62171b8e-8375-4b9c-8d69-2151bd42441c
-- title:
--   Prof Coh: coind Homotopy identity
-- statement:
--   The Prof Coh construction uses the coind Homotopy identity property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CoinducedModules/Acyclic.lean#L128-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/CoinducedModules/Acyclic.lean#L128-L136

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains_Functoriality
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules_Acyclic
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
open CategoryTheory groupCohomology Filter Topology
universe u
variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] {X : Type u} [AddCommGroup X] [Module k X]

theorem GroundTheory.ProfCoh.coindHomotopy_identity (n : ℕ)
    (f : locallyConstantCochains (discreteCoind k G X) (n + 1)) :
    (dLocallyConstant (discreteCoind k G X) n).hom (coindHomotopy k X n f) +
      coindHomotopy k X (n + 1) ((dLocallyConstant (discreteCoind k G X) (n + 1)).hom f) = f := by sorry
