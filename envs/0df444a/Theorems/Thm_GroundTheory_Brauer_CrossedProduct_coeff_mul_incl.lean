-- Prove2me | Theorems.Thm_GroundTheory_Brauer_CrossedProduct_coeff_mul_incl
-- name    : GroundTheory.Brauer.CrossedProduct.coeff_mul_incl
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:37:08.764799+00:00
-- url     : https://prove2.me/theorems/52095e6d-02a9-42cf-8b5b-b716bc858d97
-- title:
--   Crossed Product: coeff mul incl
-- statement:
--   The Crossed Product construction uses the coeff mul incl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProduct.lean#L306-L315
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProduct.lean#L306-L315

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

theorem GroundTheory.Brauer.CrossedProduct.coeff_mul_incl (x : CrossedProduct hf) (b : L) (σ : L ≃ₐ[K] L) :
    (x * incl b).coeff σ = x.coeff σ * σ b := by sorry
