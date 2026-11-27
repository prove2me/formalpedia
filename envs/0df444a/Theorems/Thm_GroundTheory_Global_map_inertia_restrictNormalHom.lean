-- Prove2me | Theorems.Thm_GroundTheory_Global_map_inertia_restrictNormalHom
-- name    : GroundTheory.Global.map_inertia_restrictNormalHom
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:55:54.11182+00:00
-- url     : https://prove2.me/theorems/758325b2-e08f-536a-aeac-d3d271f2780e
-- title:
--   Global: map inertia restrict Normal Hom
-- statement:
--   The Global construction uses the map inertia restrict Normal Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/InflationTower.lean#L172-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/InflationTower.lean#L172-L181

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_Artin_MemInvariantsCompSubtypeIff
import Definitions.Def_GroundTheory_GlobalFields_Artin_InflationTower
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open IsDedekindDomain NumberField
open scoped Pointwise
open GroundTheory GroundTheory.Global
variable {K F L : Type*} [Field K] [NumberField K] [Field F] [NumberField F] [Field L]
  [NumberField L] [Algebra K F] [Algebra K L] [Algebra F L] [IsScalarTower K F L]
  [IsGalois K F] [IsGalois K L]

theorem GroundTheory.Global.map_inertia_restrictNormalHom (Q : Ideal (𝓞 L)) [Q.IsPrime] :
    (Q.inertia Gal(L/K)).map (AlgEquiv.restrictNormalHom F) =
      (Q.under (𝓞 F)).inertia Gal(F/K) := by sorry
