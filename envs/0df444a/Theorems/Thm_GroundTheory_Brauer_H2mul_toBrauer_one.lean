-- Prove2me | Theorems.Thm_GroundTheory_Brauer_H2mul_toBrauer_one
-- name    : GroundTheory.Brauer.H2mul.toBrauer_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T07:49:41.1719+00:00
-- url     : https://prove2.me/theorems/6c6ba337-15fe-4910-8491-f0994ca44e2c
-- title:
--   H2mul: to Brauer one
-- statement:
--   The H2mul construction uses the to Brauer one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProductInj.lean#L190-L191
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProductInj.lean#L190-L191

import Mathlib
import Definitions.Def_GroundTheory_Brauer_CrossedProduct
import Definitions.Def_GroundTheory_Brauer_CrossedProductSimple
import Definitions.Def_GroundTheory_Brauer_CrossedProductMaps
import Definitions.Def_GroundTheory_Brauer_SkolemNoether
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Definitions.Def_GroundTheory_Brauer_MulDistribMulActionQuotientFixedPoints
import Definitions.Def_GroundTheory_Brauer_CrossedProductInj
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
universe u v
open GroundTheory.Brauer.H2mul
variable (K L : Type u) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
variable {K L}

theorem GroundTheory.Brauer.H2mul.toBrauer_one : toBrauer K L (1 : H2mul (L ≃ₐ[K] L) Lˣ) = 1 := by sorry
