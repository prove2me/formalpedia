-- Prove2me | Theorems.Thm_GroundTheory_Global_restrictNormalHom_restrictScalars
-- name    : GroundTheory.Global.restrictNormalHom_restrictScalars
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:58:50.718849+00:00
-- url     : https://prove2.me/theorems/092e4081-c2d6-4524-bacf-ff626e7376dc
-- title:
--   Global: restrict Normal Hom restrict Scalars
-- statement:
--   The Global construction uses the restrict Normal Hom restrict Scalars property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/InflationTower.lean#L76-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/InflationTower.lean#L76-L81

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
omit [NumberField K] [NumberField F] [NumberField L] [IsGalois K L]

theorem GroundTheory.Global.restrictNormalHom_restrictScalars (g : Gal(L/F)) :
    AlgEquiv.restrictNormalHom F (g.restrictScalars K) = 1 := by sorry
