-- Prove2me | Theorems.Thm_GroundTheory_Brauer_CrossedProduct_eq_single_of_mul_incl
-- name    : GroundTheory.Brauer.CrossedProduct.eq_single_of_mul_incl
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T07:47:23.886797+00:00
-- url     : https://prove2.me/theorems/aa9112a3-2ef9-527d-b399-067dfaa52b5a
-- title:
--   Crossed Product: eq single of mul incl
-- statement:
--   The Crossed Product construction uses the eq single of mul incl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProductInj.lean#L23-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProductInj.lean#L23-L37

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
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
variable {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ} {hf : IsMulCocycle₂ f}

theorem GroundTheory.Brauer.CrossedProduct.eq_single_of_mul_incl (σ : L ≃ₐ[K] L) (x : CrossedProduct hf)
    (hx : ∀ b : L, x * incl b = incl (σ b) * x) : x = single σ (x.coeff σ) := by sorry
