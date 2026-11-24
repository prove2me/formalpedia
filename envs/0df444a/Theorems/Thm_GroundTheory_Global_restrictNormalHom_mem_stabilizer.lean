-- Prove2me | Theorems.Thm_GroundTheory_Global_restrictNormalHom_mem_stabilizer
-- name    : GroundTheory.Global.restrictNormalHom_mem_stabilizer
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:42:35.749808+00:00
-- url     : https://prove2.me/theorems/13fba164-0861-4be1-8c56-fac76edbea83
-- title:
--   Global: restrict Normal Hom mem stabilizer
-- statement:
--   The Global construction uses the restrict Normal Hom mem stabilizer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/InflationTower.lean#L92-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/InflationTower.lean#L92-L96

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

theorem GroundTheory.Global.restrictNormalHom_mem_stabilizer {Q : Ideal (𝓞 L)} {σ : Gal(L/K)}
    (hσ : σ ∈ MulAction.stabilizer Gal(L/K) Q) :
    AlgEquiv.restrictNormalHom F σ ∈ MulAction.stabilizer Gal(F/K) (Q.under (𝓞 F)) := by sorry
