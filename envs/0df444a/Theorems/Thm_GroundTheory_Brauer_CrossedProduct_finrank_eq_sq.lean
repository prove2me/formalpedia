-- Prove2me | Theorems.Thm_GroundTheory_Brauer_CrossedProduct_finrank_eq_sq
-- name    : GroundTheory.Brauer.CrossedProduct.finrank_eq_sq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:41:13.619827+00:00
-- url     : https://prove2.me/theorems/1f90868d-e226-4d31-8fb4-bee5f8c7615e
-- title:
--   Crossed Product: finrank eq sq
-- statement:
--   The Crossed Product construction uses the finrank eq sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProduct.lean#L353-L356
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/Brauer/CrossedProduct.lean#L353-L356

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

theorem GroundTheory.Brauer.CrossedProduct.finrank_eq_sq [FiniteDimensional K L] [IsGalois K L] :
    Module.finrank K (CrossedProduct hf) = Module.finrank K L ^ 2 := by sorry
