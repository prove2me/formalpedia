-- Prove2me | Theorems.Thm_GroundTheory_ProfCoh_h2GalUnitsAddEquiv_H2_class
-- name    : GroundTheory.ProfCoh.h2GalUnitsAddEquiv_H2_class
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T13:07:00.348379+00:00
-- url     : https://prove2.me/theorems/5ba0e82a-d3d7-5954-9c81-347dd7627244
-- title:
--   Prof Coh: h2 Gal Units Add Equiv H2 class
-- statement:
--   The Prof Coh construction uses the h2 Gal Units Add Equiv H2 class property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalClassFormation/OrderScalars.lean#L91-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/ProfiniteCohomology/LocalClassFormation/OrderScalars.lean#L91-L94

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
variable (K L : Type) [Field K] [Field L] [Algebra K L]

theorem GroundTheory.ProfCoh.h2GalUnitsAddEquiv_H2_class (x : cocycles₂ (galUnits K L)) :
    h2GalUnitsAddEquiv K L ((H2π _).hom x) =
      (H2π _).hom (cocycles₂IntRepAddEquiv (galUnitsHom K L) x) := by sorry
