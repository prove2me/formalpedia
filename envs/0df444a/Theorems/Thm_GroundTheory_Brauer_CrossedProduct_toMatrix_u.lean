-- Prove2me | Theorems.Thm_GroundTheory_Brauer_CrossedProduct_toMatrix_u
-- name    : GroundTheory.Brauer.CrossedProduct.toMatrix_u
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T06:08:38.161686+00:00
-- url     : https://prove2.me/theorems/1bd4a3f6-9732-5e9b-9c00-2472880361df
-- title:
--   Crossed Product: to Matrix u
-- statement:
--   The Crossed Product construction uses the to Matrix u property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProductRegular.lean#L129-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProductRegular.lean#L129-L130

import Mathlib
import Definitions.Def_GroundTheory_Brauer_CrossedProduct
import Definitions.Def_GroundTheory_Brauer_CrossedProductSimple
import Definitions.Def_GroundTheory_Brauer_CrossedProductMaps
import Definitions.Def_GroundTheory_Brauer_CrossedProductRegular
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
open GroundTheory.Brauer.CrossedProduct
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
  [DecidableEq (L ≃ₐ[K] L)]
variable {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ}
variable {C : Type*} [Ring C] [Algebra K C] (j : L →ₐ[K] C)
variable (hf : IsMulCocycle₂ f)

theorem GroundTheory.Brauer.CrossedProduct.toMatrix_u (σ : L ≃ₐ[K] L) : toMatrix j hf (u σ) = regularU j f σ := by sorry
