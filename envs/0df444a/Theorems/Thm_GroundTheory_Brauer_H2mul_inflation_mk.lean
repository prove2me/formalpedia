-- Prove2me | Theorems.Thm_GroundTheory_Brauer_H2mul_inflation_mk
-- name    : GroundTheory.Brauer.H2mul.inflation_mk
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T09:44:03.138547+00:00
-- url     : https://prove2.me/theorems/cca1d986-db3a-5e5e-ad67-c30ccd624318
-- title:
--   H2mul: inflation mk
-- statement:
--   The H2mul construction uses the inflation mk property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Inflation.lean#L238-L242
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/Inflation.lean#L238-L242

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
variable (K L L' : Type*) [Field K] [Field L] [Field L'] [Algebra K L] [Algebra K L']
  [Algebra L L'] [IsScalarTower K L L'] [Normal K L]
variable {K L L'}

theorem GroundTheory.Brauer.H2mul.inflation_mk (c : mulCocycles₂ (L ≃ₐ[K] L) Lˣ) :
    inflation K L L' (mk _ _ c) =
      mk _ _ ⟨CrossedProduct.inflate L' (c : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ),
        CrossedProduct.isMulCocycle₂_inflate L' c.2⟩ := by sorry
