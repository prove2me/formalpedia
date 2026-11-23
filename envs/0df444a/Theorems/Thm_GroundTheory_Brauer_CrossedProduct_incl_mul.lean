-- Prove2me | Theorems.Thm_GroundTheory_Brauer_CrossedProduct_incl_mul
-- name    : GroundTheory.Brauer.CrossedProduct.incl_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:55:24.776792+00:00
-- url     : https://prove2.me/theorems/7fa7e4b9-3a1c-423b-877d-8cc3ce3b9574
-- title:
--   Crossed Product: incl mul
-- statement:
--   The Crossed Product construction uses the incl mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProduct.lean#L272-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProduct.lean#L272-L273

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

theorem GroundTheory.Brauer.CrossedProduct.incl_mul (a : L) (x : CrossedProduct hf) : incl a * x = a • x := by sorry
