-- Prove2me | Theorems.Thm_GroundTheory_Brauer_CrossedProduct_incl_eq_smul_one
-- name    : GroundTheory.Brauer.CrossedProduct.incl_eq_smul_one
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:36:45.529475+00:00
-- url     : https://prove2.me/theorems/624f730a-e311-4d61-91a0-51472b133c6a
-- title:
--   Crossed Product: incl eq smul one
-- statement:
--   The Crossed Product construction uses the incl eq smul one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProduct.lean#L269-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProduct.lean#L269-L270

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

theorem GroundTheory.Brauer.CrossedProduct.incl_eq_smul_one (a : L) : (incl a : CrossedProduct hf) = a • 1 := by sorry
