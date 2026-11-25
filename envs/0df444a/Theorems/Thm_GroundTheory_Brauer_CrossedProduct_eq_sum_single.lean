-- Prove2me | Theorems.Thm_GroundTheory_Brauer_CrossedProduct_eq_sum_single
-- name    : GroundTheory.Brauer.CrossedProduct.eq_sum_single
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:54:27.082928+00:00
-- url     : https://prove2.me/theorems/fb25ac43-4559-4b4a-a751-1e3deeb296dc
-- title:
--   Crossed Product: eq sum single
-- statement:
--   The Crossed Product construction uses the eq sum single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProduct.lean#L235-L240
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProduct.lean#L235-L240

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

theorem GroundTheory.Brauer.CrossedProduct.eq_sum_single (x : CrossedProduct hf) :
    x = x.coeff.sum fun σ a => single σ a := by sorry
