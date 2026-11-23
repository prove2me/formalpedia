-- Prove2me | Theorems.Thm_GroundTheory_Brauer_CrossedProduct_u_mul_u
-- name    : GroundTheory.Brauer.CrossedProduct.u_mul_u
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:40:42.897854+00:00
-- url     : https://prove2.me/theorems/81705407-bda7-49f1-8f11-f28a4c0aeb80
-- title:
--   Crossed Product: u mul u
-- statement:
--   The Crossed Product construction uses the u mul u property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProduct.lean#L298-L301
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProduct.lean#L298-L301

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

theorem GroundTheory.Brauer.CrossedProduct.u_mul_u (σ τ : L ≃ₐ[K] L) :
    (u σ : CrossedProduct hf) * u τ = incl (f (σ, τ) : L) * u (σ * τ) := by sorry
