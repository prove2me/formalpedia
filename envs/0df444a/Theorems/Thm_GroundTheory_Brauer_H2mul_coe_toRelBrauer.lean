-- Prove2me | Theorems.Thm_GroundTheory_Brauer_H2mul_coe_toRelBrauer
-- name    : GroundTheory.Brauer.H2mul.coe_toRelBrauer
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T09:05:49.30425+00:00
-- url     : https://prove2.me/theorems/f8e4cd82-03e2-5d2f-8e68-4c95b03b94ae
-- title:
--   H2mul: coe to Rel Brauer
-- statement:
--   The H2mul construction uses the coe to Rel Brauer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProductTensor.lean#L298-L299
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProductTensor.lean#L298-L299

import Mathlib
import Definitions.Def_GroundTheory_Brauer_CrossedProduct
import Definitions.Def_GroundTheory_Brauer_CrossedProductSimple
import Definitions.Def_GroundTheory_Brauer_CrossedProductMaps
import Definitions.Def_GroundTheory_Brauer_CrossedProductRegular
import Definitions.Def_GroundTheory_Brauer_CrossedProductInj
import Definitions.Def_GroundTheory_Brauer_TensorSimple
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Definitions.Def_GroundTheory_Brauer_BaseChangeCSA
import Definitions.Def_GroundTheory_Brauer_BaseChange
import Definitions.Def_GroundTheory_Brauer_MulDistribMulActionQuotientFixedPoints
import Definitions.Def_GroundTheory_Brauer_CrossedProductTensor
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Brauer
open groupCohomology TensorProduct
universe u
variable {K L : Type u} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
open GroundTheory.Brauer.H2mul

theorem GroundTheory.Brauer.H2mul.coe_toRelBrauer (x : H2mul (L ≃ₐ[K] L) Lˣ) :
    (toRelBrauer K L x : BrauerGroup.{u, u} K) = toBrauer K L x := by sorry

attribute [defeq] GroundTheory.Brauer.H2mul.coe_toRelBrauer
