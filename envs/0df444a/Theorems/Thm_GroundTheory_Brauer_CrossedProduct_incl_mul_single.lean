-- Prove2me | Theorems.Thm_GroundTheory_Brauer_CrossedProduct_incl_mul_single
-- name    : GroundTheory.Brauer.CrossedProduct.incl_mul_single
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:02:07.176469+00:00
-- url     : https://prove2.me/theorems/ff76f233-cb55-4e0c-8134-180d32ece5db
-- title:
--   Crossed Product: incl mul single
-- statement:
--   The Crossed Product construction uses the incl mul single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProduct.lean#L281-L283
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProduct.lean#L281-L283

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

theorem GroundTheory.Brauer.CrossedProduct.incl_mul_single (a : L) (σ : L ≃ₐ[K] L) (b : L) :
    (incl a : CrossedProduct hf) * single σ b = single σ (a * b) := by sorry
