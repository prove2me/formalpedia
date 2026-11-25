-- Prove2me | Theorems.Thm_GroundTheory_Brauer_CrossedProduct_isUnit_u
-- name    : GroundTheory.Brauer.CrossedProduct.isUnit_u
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:55:17.688898+00:00
-- url     : https://prove2.me/theorems/aa11f46a-e8a0-41d0-8727-ac04da8f8215
-- title:
--   Crossed Product: is Unit u
-- statement:
--   The Crossed Product construction uses the is Unit u property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProduct.lean#L321-L332
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProduct.lean#L321-L332

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

theorem GroundTheory.Brauer.CrossedProduct.isUnit_u (σ : L ≃ₐ[K] L) : IsUnit (u σ : CrossedProduct hf) := by sorry
