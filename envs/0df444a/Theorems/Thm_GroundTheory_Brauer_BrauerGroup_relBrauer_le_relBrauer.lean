-- Prove2me | Theorems.Thm_GroundTheory_Brauer_BrauerGroup_relBrauer_le_relBrauer
-- name    : GroundTheory.Brauer.BrauerGroup.relBrauer_le_relBrauer
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T09:41:59.173175+00:00
-- url     : https://prove2.me/theorems/54b7ca8c-f58b-47e0-b59e-edbcb07b7af2
-- title:
--   Brauer Group: rel Brauer le rel Brauer
-- statement:
--   The Brauer Group construction uses the rel Brauer le rel Brauer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Inflation.lean#L218-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Inflation.lean#L218-L221

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
open GroundTheory.Brauer.BrauerGroup
variable (K L L' : Type u) [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']
  [Algebra L L'] [IsScalarTower K L L']

theorem GroundTheory.Brauer.BrauerGroup.relBrauer_le_relBrauer : relBrauer K L ≤ relBrauer K L' := by sorry
