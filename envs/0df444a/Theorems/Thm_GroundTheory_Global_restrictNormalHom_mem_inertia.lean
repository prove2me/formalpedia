-- Prove2me | Theorems.Thm_GroundTheory_Global_restrictNormalHom_mem_inertia
-- name    : GroundTheory.Global.restrictNormalHom_mem_inertia
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:42:40.789547+00:00
-- url     : https://prove2.me/theorems/90cb1030-fc11-49ed-b978-e2f736a99fdd
-- title:
--   Global: restrict Normal Hom mem inertia
-- statement:
--   The Global construction uses the restrict Normal Hom mem inertia property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/InflationTower.lean#L100-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/InflationTower.lean#L100-L107

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

theorem GroundTheory.Global.restrictNormalHom_mem_inertia {Q : Ideal (𝓞 L)} {σ : Gal(L/K)}
    (hσ : σ ∈ Q.inertia Gal(L/K)) :
    AlgEquiv.restrictNormalHom F σ ∈ (Q.under (𝓞 F)).inertia Gal(F/K) := by sorry
