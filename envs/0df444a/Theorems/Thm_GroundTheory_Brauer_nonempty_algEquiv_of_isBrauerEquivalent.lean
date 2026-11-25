-- Prove2me | Theorems.Thm_GroundTheory_Brauer_nonempty_algEquiv_of_isBrauerEquivalent
-- name    : GroundTheory.Brauer.nonempty_algEquiv_of_isBrauerEquivalent
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T06:11:45.057278+00:00
-- url     : https://prove2.me/theorems/9ba6f3cf-9e88-5ccc-bbfa-6b363995e6bc
-- title:
--   Brauer: nonempty alg Equiv of is Brauer Equivalent
-- statement:
--   The Brauer construction uses the nonempty alg Equiv of is Brauer Equivalent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProductInj.lean#L89-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProductInj.lean#L89-L105

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

theorem GroundTheory.Brauer.nonempty_algEquiv_of_isBrauerEquivalent {K : Type u} [Field K] {A B : CSA.{u, v} K}
    (h : IsBrauerEquivalent A B) (hd : Module.finrank K A = Module.finrank K B) :
    Nonempty (A ≃ₐ[K] B) := by sorry
