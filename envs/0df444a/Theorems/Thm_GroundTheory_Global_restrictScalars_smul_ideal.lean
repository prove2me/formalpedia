-- Prove2me | Theorems.Thm_GroundTheory_Global_restrictScalars_smul_ideal
-- name    : GroundTheory.Global.restrictScalars_smul_ideal
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:43:04.355995+00:00
-- url     : https://prove2.me/theorems/99c3cc1a-b53d-45a9-80e5-19dfcf9f9cda
-- title:
--   Global: restrict Scalars smul ideal
-- statement:
--   The Global construction uses the restrict Scalars smul ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/InflationTower.lean#L85-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/InflationTower.lean#L85-L88

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
omit [NumberField K] [NumberField F] [NumberField L] [IsGalois K F] [IsGalois K L]

theorem GroundTheory.Global.restrictScalars_smul_ideal (g : Gal(L/F)) (I : Ideal (𝓞 L)) :
    g.restrictScalars K • I = g • I := by sorry
