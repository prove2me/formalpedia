-- Prove2me | Theorems.Thm_GroundTheory_Brauer_CrossedProduct_isBrauerEquivalent_one_one
-- name    : GroundTheory.Brauer.CrossedProduct.isBrauerEquivalent_one_one
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T06:15:54.315043+00:00
-- url     : https://prove2.me/theorems/a4c6dddd-447a-4c4e-beab-d8cd345d6d15
-- title:
--   Crossed Product: is Brauer Equivalent one one
-- statement:
--   The Crossed Product construction uses the is Brauer Equivalent one one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProductInj.lean#L112-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProductInj.lean#L112-L117

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
open GroundTheory.Brauer.CrossedProduct
variable {K L : Type u} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
variable {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ}

theorem GroundTheory.Brauer.CrossedProduct.isBrauerEquivalent_one_one :
    IsBrauerEquivalent (csaOf K (CrossedProduct (isMulCocycle₂_one (K := K) (L := L))))
      (oneCSA K) := by sorry
