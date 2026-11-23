-- Prove2me | Theorems.Thm_GroundTheory_Global_algebraMap_restrictNormalHom_smul
-- name    : GroundTheory.Global.algebraMap_restrictNormalHom_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:25:14.66253+00:00
-- url     : https://prove2.me/theorems/9bbdc86e-5bc7-4d6c-8f02-5acf827e4897
-- title:
--   Global: algebra Map restrict Normal Hom smul
-- statement:
--   The Global construction uses the algebra Map restrict Normal Hom smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/InflationTower.lean#L59-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/InflationTower.lean#L59-L64

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

theorem GroundTheory.Global.algebraMap_restrictNormalHom_smul (σ : Gal(L/K)) (x : 𝓞 F) :
    algebraMap (𝓞 F) (𝓞 L) (AlgEquiv.restrictNormalHom F σ • x) =
      σ • algebraMap (𝓞 F) (𝓞 L) x := by sorry
