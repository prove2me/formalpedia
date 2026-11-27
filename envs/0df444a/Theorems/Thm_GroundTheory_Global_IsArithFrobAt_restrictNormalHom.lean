-- Prove2me | Theorems.Thm_GroundTheory_Global_IsArithFrobAt_restrictNormalHom
-- name    : GroundTheory.Global.IsArithFrobAt.restrictNormalHom
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:55:25.750752+00:00
-- url     : https://prove2.me/theorems/7d28b51e-373b-47ea-b394-93ce673735a3
-- title:
--   Is Arith Frob At: restrict Normal Hom
-- statement:
--   The Is Arith Frob At construction uses the restrict Normal Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/InflationTower.lean#L183-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/Artin/InflationTower.lean#L183-L191

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

theorem GroundTheory.Global.IsArithFrobAt.restrictNormalHom {φ : Gal(L/K)} {Q : Ideal (𝓞 L)}
    (h : IsArithFrobAt (𝓞 K) φ Q) :
    IsArithFrobAt (𝓞 K) (AlgEquiv.restrictNormalHom F φ) (Q.under (𝓞 F)) := by sorry
