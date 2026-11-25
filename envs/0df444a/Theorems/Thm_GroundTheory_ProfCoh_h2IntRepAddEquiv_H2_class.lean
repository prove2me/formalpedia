-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_h2IntRepAddEquiv_H2_class
-- name    : GroundTheory.ProfCoh.h2IntRepAddEquiv_H2_class
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:50:58.267876+00:00
-- url     : https://prove2.me/theorems/5be472aa-159f-431d-a759-e72d4e00e4f3
-- title:
--   Prof Coh: h2 Int Rep Add Equiv H2 class
-- statement:
--   The Prof Coh construction uses the h2 Int Rep Add Equiv H2 class property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalClassFormation/OrderScalars.lean#L71-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalClassFormation/OrderScalars.lean#L71-L79

import Mathlib
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_Discrete
import Definitions.Def_GroundTheory_ProfiniteCohomology_GaloisModules_FixedField
import Definitions.Def_GroundTheory_ProfiniteCohomology_LocalClassFormation_OrderScalars
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
variable {G M : Type} [Group G] [CommGroup M] (φ : G →* Monoid.End M)

theorem GroundTheory.ProfCoh.h2IntRepAddEquiv_H2_class (x : cocycles₂ (Rep.of (intRepOfMonoidEnd.{0} φ))) :
    h2IntRepAddEquiv φ ((H2π _).hom x) = (H2π _).hom (cocycles₂IntRepAddEquiv φ x) := by sorry
