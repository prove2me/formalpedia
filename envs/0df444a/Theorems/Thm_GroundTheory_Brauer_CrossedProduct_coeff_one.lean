-- Prove2me | Theorems.Thm_GroundTheory_Brauer_CrossedProduct_coeff_one
-- name    : GroundTheory.Brauer.CrossedProduct.coeff_one
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:54:34.791995+00:00
-- url     : https://prove2.me/theorems/88906a7b-7bd1-4a21-9ed9-5176d5a7315c
-- title:
--   Crossed Product: coeff one
-- statement:
--   The Crossed Product construction uses the coeff one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProduct.lean#L166-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProduct.lean#L166-L167

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

theorem GroundTheory.Brauer.CrossedProduct.coeff_one :
    (1 : CrossedProduct hf).coeff = Finsupp.single 1 (((f (1, 1))⁻¹ : Lˣ) : L) := by sorry
