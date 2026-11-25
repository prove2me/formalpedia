-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_isAddTorsion_discreteCoind
-- name    : GroundTheory.ProfCoh.isAddTorsion_discreteCoind
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:33:29.469561+00:00
-- url     : https://prove2.me/theorems/2336ebfe-f48c-4207-aa59-a041b98f1fd5
-- title:
--   Prof Coh: is Add Torsion discrete Coind
-- statement:
--   The Prof Coh construction uses the is Add Torsion discrete Coind property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/Procyclic.lean#L390-L402
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/Procyclic.lean#L390-L402

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

theorem GroundTheory.ProfCoh.isAddTorsion_discreteCoind (X : Type u) [AddCommGroup X] [Module k X]
    (hX : IsAddTorsion X) : IsAddTorsion (discreteCoind k G X) := by sorry
