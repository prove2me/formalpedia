-- Prove2me | Theorems.Thm_GroundTheory_Brauer_H2mul_toBrauer_inflation
-- name    : GroundTheory.Brauer.H2mul.toBrauer_inflation
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:44:04.250444+00:00
-- url     : https://prove2.me/theorems/7152c7b1-9b34-51cd-a71e-408b3db5f015
-- title:
--   H2mul: to Brauer inflation
-- statement:
--   The H2mul construction uses the to Brauer inflation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Inflation.lean#L252-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Inflation.lean#L252-L257

import Mathlib
import Definitions.Def_GroundTheory_Brauer_CrossedProduct
import Definitions.Def_GroundTheory_Brauer_CrossedProductSimple
import Definitions.Def_GroundTheory_Brauer_CrossedProductMaps
import Definitions.Def_GroundTheory_Brauer_CrossedProductInj
import Definitions.Def_GroundTheory_Brauer_CrossedProductTensor
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Definitions.Def_GroundTheory_Brauer_BaseChange
import Definitions.Def_GroundTheory_Brauer_MulDistribMulActionQuotientFixedPoints
import Definitions.Def_GroundTheory_Brauer_Inflation
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
open groupCohomology
universe u
open GroundTheory.Brauer.H2mul
variable {K L L' : Type u} [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']
  [Algebra L L'] [IsScalarTower K L L'] [FiniteDimensional K L] [IsGalois K L]
  [FiniteDimensional K L'] [IsGalois K L']

theorem GroundTheory.Brauer.H2mul.toBrauer_inflation (x : H2mul (L ≃ₐ[K] L) Lˣ) :
    toBrauer K L' (inflation K L L' x) = toBrauer K L x := by sorry
