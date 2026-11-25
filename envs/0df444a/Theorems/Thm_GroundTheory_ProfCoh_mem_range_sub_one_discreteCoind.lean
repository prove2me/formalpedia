-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_mem_range_sub_one_discreteCoind
-- name    : GroundTheory.ProfCoh.mem_range_sub_one_discreteCoind
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:59:50.945397+00:00
-- url     : https://prove2.me/theorems/a95676b6-11d2-49e4-a568-8c18db3d4a02
-- title:
--   Prof Coh: mem range sub one discrete Coind
-- statement:
--   The Prof Coh construction uses the mem range sub one discrete Coind property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/Procyclic.lean#L406-L415
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/Procyclic.lean#L406-L415

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_ProcyclicDefs
import Definitions.Def_GroundTheory_ProfiniteCohomology_ContinuousCochains_Functoriality
import Definitions.Def_GroundTheory_ProfiniteCohomology_CoinducedModules_CohomologyCoindCokernelIsoHom
import Definitions.Def_GroundTheory_ProfiniteCohomology_CohomologicalDimension_PrimaryComponentCohomologyEqBotOfScdpLt
import Definitions.Def_GroundTheory_ProfiniteCohomology_Procyclic
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
open CategoryTheory Limits groupCohomology
universe u
variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G]
variable {σ : G}

theorem GroundTheory.ProfCoh.mem_range_sub_one_discreteCoind (hσ : IsZHatGenerator σ) (A : Rep.{u} k G)
    [IsDiscreteRep A] (hA : IsAddTorsion A) (c : LocallyConstant G A) :
    c ∈ LinearMap.range ((discreteCoind k G A).ρ σ - 1) := by sorry
