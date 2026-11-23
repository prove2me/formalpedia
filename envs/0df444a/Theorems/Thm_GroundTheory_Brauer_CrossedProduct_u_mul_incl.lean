-- Prove2me | Theorems.Thm_GroundTheory_Brauer_CrossedProduct_u_mul_incl
-- name    : GroundTheory.Brauer.CrossedProduct.u_mul_incl
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T06:02:22.474586+00:00
-- url     : https://prove2.me/theorems/213a1d42-dc5b-4fe5-a780-a167cf77c8ba
-- title:
--   Crossed Product: u mul incl
-- statement:
--   The Crossed Product construction uses the u mul incl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProduct.lean#L293-L296
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProduct.lean#L293-L296

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

theorem GroundTheory.Brauer.CrossedProduct.u_mul_incl (σ : L ≃ₐ[K] L) (a : L) :
    (u σ : CrossedProduct hf) * incl a = incl (σ a) * u σ := by sorry
