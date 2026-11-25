-- Prove2me | Theorems.Thm_GroundTheory_Brauer_CrossedProduct_single_eq_smul_u
-- name    : GroundTheory.Brauer.CrossedProduct.single_eq_smul_u
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:54:23.322365+00:00
-- url     : https://prove2.me/theorems/2c897f87-2a53-5545-bd49-da8c69755f7f
-- title:
--   Crossed Product: single eq smul u
-- statement:
--   The Crossed Product construction uses the single eq smul u property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProduct.lean#L217-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProduct.lean#L217-L219

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

theorem GroundTheory.Brauer.CrossedProduct.single_eq_smul_u (σ : L ≃ₐ[K] L) (a : L) :
    (single σ a : CrossedProduct hf) = a • u σ := by sorry
