-- Prove2me | Theorems.Thm_GroundTheory_Global_exists_mem_inertia_restrictNormalHom_eq
-- name    : GroundTheory.Global.exists_mem_inertia_restrictNormalHom_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T23:41:38.91437+00:00
-- url     : https://prove2.me/theorems/4908509c-dda6-4031-a7cd-cbfeb45c64ac
-- title:
--   Global: exists mem inertia restrict Normal Hom eq
-- statement:
--   The Global construction uses the exists mem inertia restrict Normal Hom eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/InflationTower.lean#L123-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/InflationTower.lean#L123-L157

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

theorem GroundTheory.Global.exists_mem_inertia_restrictNormalHom_eq (Q : Ideal (𝓞 L)) [Q.IsPrime]
    {τ : Gal(F/K)} (hτ : τ ∈ (Q.under (𝓞 F)).inertia Gal(F/K)) :
    ∃ σ ∈ Q.inertia Gal(L/K), AlgEquiv.restrictNormalHom F σ = τ := by sorry
