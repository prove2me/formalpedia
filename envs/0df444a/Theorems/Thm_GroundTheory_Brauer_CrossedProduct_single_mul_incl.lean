-- Prove2me | Theorems.Thm_GroundTheory_Brauer_CrossedProduct_single_mul_incl
-- name    : GroundTheory.Brauer.CrossedProduct.single_mul_incl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:56:13.60497+00:00
-- url     : https://prove2.me/theorems/271dd4dd-2158-47dd-8866-20fd9ea256fd
-- title:
--   Crossed Product: single mul incl
-- statement:
--   The Crossed Product construction uses the single mul incl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProduct.lean#L288-L291
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProduct.lean#L288-L291

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

theorem GroundTheory.Brauer.CrossedProduct.single_mul_incl (σ : L ≃ₐ[K] L) (a b : L) :
    (single σ a : CrossedProduct hf) * incl b = single σ (a * σ b) := by sorry
