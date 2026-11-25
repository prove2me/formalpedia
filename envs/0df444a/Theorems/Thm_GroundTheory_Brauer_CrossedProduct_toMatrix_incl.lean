-- Prove2me | Theorems.Thm_GroundTheory_Brauer_CrossedProduct_toMatrix_incl
-- name    : GroundTheory.Brauer.CrossedProduct.toMatrix_incl
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T06:09:58.112229+00:00
-- url     : https://prove2.me/theorems/2977b8b3-2d35-449a-ab92-75d5898ac3d7
-- title:
--   Crossed Product: to Matrix incl
-- statement:
--   The Crossed Product construction uses the to Matrix incl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProductRegular.lean#L125-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProductRegular.lean#L125-L127

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

theorem GroundTheory.Brauer.CrossedProduct.toMatrix_incl (a : L) :
    toMatrix j hf (incl a) = diagHom (fun ρ => j.comp (ρ⁻¹ : L ≃ₐ[K] L).toAlgHom) a := by sorry
