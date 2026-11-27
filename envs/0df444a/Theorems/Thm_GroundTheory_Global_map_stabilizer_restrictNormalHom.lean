-- Prove2me | Theorems.Thm_GroundTheory_Global_map_stabilizer_restrictNormalHom
-- name    : GroundTheory.Global.map_stabilizer_restrictNormalHom
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:55:51.646387+00:00
-- url     : https://prove2.me/theorems/e065f772-c4c6-5c58-9f22-6c65c9b2f108
-- title:
--   Global: map stabilizer restrict Normal Hom
-- statement:
--   The Global construction uses the map stabilizer restrict Normal Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/InflationTower.lean#L161-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/InflationTower.lean#L161-L170

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
omit [NumberField K]

theorem GroundTheory.Global.map_stabilizer_restrictNormalHom (Q : Ideal (𝓞 L)) [Q.IsPrime] :
    (MulAction.stabilizer Gal(L/K) Q).map (AlgEquiv.restrictNormalHom F) =
      MulAction.stabilizer Gal(F/K) (Q.under (𝓞 F)) := by sorry
