-- Prove2me | Theorems.Thm_GroundTheory_Brauer_CrossedProduct_basis_apply
-- name    : GroundTheory.Brauer.CrossedProduct.basis_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:01:59.175024+00:00
-- url     : https://prove2.me/theorems/2c100c6f-06b1-4216-b2af-0481f3f9484c
-- title:
--   Crossed Product: basis apply
-- statement:
--   The Crossed Product construction uses the basis apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProduct.lean#L337-L339
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProduct.lean#L337-L339

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

theorem GroundTheory.Brauer.CrossedProduct.basis_apply (σ : L ≃ₐ[K] L) : (basis σ : CrossedProduct hf) = u σ := by sorry
