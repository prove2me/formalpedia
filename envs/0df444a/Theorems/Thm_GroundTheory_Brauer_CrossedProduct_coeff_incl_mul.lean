-- Prove2me | Theorems.Thm_GroundTheory_Brauer_CrossedProduct_coeff_incl_mul
-- name    : GroundTheory.Brauer.CrossedProduct.coeff_incl_mul
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T23:37:51.20199+00:00
-- url     : https://prove2.me/theorems/6984adce-4c05-46d5-9695-d3b49a96ee09
-- title:
--   Crossed Product: coeff incl mul
-- statement:
--   The Crossed Product construction uses the coeff incl mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProduct.lean#L317-L319
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProduct.lean#L317-L319

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

theorem GroundTheory.Brauer.CrossedProduct.coeff_incl_mul (b : L) (x : CrossedProduct hf) (σ : L ≃ₐ[K] L) :
    (incl b * x).coeff σ = b * x.coeff σ := by sorry
