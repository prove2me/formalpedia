-- Prove2me | Theorems.Thm_GroundTheory_Brauer_CrossedProduct_incl_mul_u
-- name    : GroundTheory.Brauer.CrossedProduct.incl_mul_u
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:41:27.208967+00:00
-- url     : https://prove2.me/theorems/e35cc441-b476-42f0-ba7f-80db312e24c2
-- title:
--   Crossed Product: incl mul u
-- statement:
--   The Crossed Product construction uses the incl mul u property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProduct.lean#L285-L286
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProduct.lean#L285-L286

import Mathlib
import Definitions.Def_GroundTheory_Brauer_CrossedProduct
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
variable {K L : Type*} [Field K] [Field L] [Algebra K L]
open GroundTheory.Brauer.CrossedProduct
variable {f : (L ≃ₐ[K] L) × (L ≃ₐ[K] L) → Lˣ}
variable {hf : IsMulCocycle₂ f}

theorem GroundTheory.Brauer.CrossedProduct.incl_mul_u (a : L) (σ : L ≃ₐ[K] L) : (incl a : CrossedProduct hf) * u σ = single σ a := by sorry
