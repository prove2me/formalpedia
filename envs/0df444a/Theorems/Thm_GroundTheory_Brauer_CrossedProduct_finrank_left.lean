-- Prove2me | Theorems.Thm_GroundTheory_Brauer_CrossedProduct_finrank_left
-- name    : GroundTheory.Brauer.CrossedProduct.finrank_left
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:37:15.615061+00:00
-- url     : https://prove2.me/theorems/8126707a-3e82-4132-9778-0a33750e6de8
-- title:
--   Crossed Product: finrank left
-- statement:
--   The Crossed Product construction uses the finrank left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProduct.lean#L349-L351
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProduct.lean#L349-L351

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

theorem GroundTheory.Brauer.CrossedProduct.finrank_left [FiniteDimensional K L] :
    Module.finrank L (CrossedProduct hf) = Nat.card (L ≃ₐ[K] L) := by sorry
