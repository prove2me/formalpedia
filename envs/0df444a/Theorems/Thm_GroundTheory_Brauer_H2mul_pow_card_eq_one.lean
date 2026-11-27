-- Prove2me | Theorems.Thm_GroundTheory_Brauer_H2mul_pow_card_eq_one
-- name    : GroundTheory.Brauer.H2mul.pow_card_eq_one
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T12:54:58.660885+00:00
-- url     : https://prove2.me/theorems/23d28483-97d7-5b4f-931c-8753d7508110
-- title:
--   H2mul: pow card eq one
-- statement:
--   The H2mul construction uses the pow card eq one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProductIso.lean#L291-L296
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProductIso.lean#L291-L296

import Mathlib
import Definitions.Def_GroundTheory_Brauer_CrossedProduct
import Definitions.Def_GroundTheory_Brauer_CrossedProductSimple
import Definitions.Def_GroundTheory_Brauer_CrossedProductMaps
import Definitions.Def_GroundTheory_Brauer_CrossedProductInj
import Definitions.Def_GroundTheory_Brauer_CrossedProductTensor
import Definitions.Def_GroundTheory_Brauer_SkolemNoether
import Definitions.Def_GroundTheory_Brauer_DoubleCentralizer
import Definitions.Def_GroundTheory_Brauer_Splitting
import Definitions.Def_GroundTheory_Brauer_BaseChange
import Definitions.Def_GroundTheory_Brauer_IsBrauerEquivalentIffNonemptyAlgEquiv
import Definitions.Def_GroundTheory_Brauer_MulDistribMulActionQuotientFixedPoints
import Definitions.Def_GroundTheory_Brauer_CrossedProductIso
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
open TensorProduct Module groupCohomology
universe u
open GroundTheory.Brauer.H2mul

theorem GroundTheory.Brauer.H2mul.pow_card_eq_one {G M : Type*} [Group G] [Fintype G] [CommGroup M]
    [MulDistribMulAction G M] (x : H2mul G M) : x ^ Fintype.card G = 1 := by sorry
