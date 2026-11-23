-- Prove2me | Theorems.Thm_GroundTheory_Global_exists_mem_stabilizer_restrictNormalHom_eq
-- name    : GroundTheory.Global.exists_mem_stabilizer_restrictNormalHom_eq
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:58.608819+00:00
-- url     : https://prove2.me/theorems/be0c975f-83b3-4dda-af6b-b1a0d1adb085
-- title:
--   Global: exists mem stabilizer restrict Normal Hom eq
-- statement:
--   The Global construction uses the exists mem stabilizer restrict Normal Hom eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/InflationTower.lean#L111-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/InflationTower.lean#L111-L121

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

theorem GroundTheory.Global.exists_mem_stabilizer_restrictNormalHom_eq (Q : Ideal (𝓞 L)) [Q.IsPrime]
    {τ : Gal(F/K)} (hτ : τ ∈ MulAction.stabilizer Gal(F/K) (Q.under (𝓞 F))) :
    ∃ σ ∈ MulAction.stabilizer Gal(L/K) Q, AlgEquiv.restrictNormalHom F σ = τ := by sorry
