-- Prove2me | Theorems.Thm_GlobalTheory_GaloisDescent_baseChange_eq_span_image
-- name    : GlobalTheory.GaloisDescent.baseChange_eq_span_image
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:52:14.009023+00:00
-- url     : https://prove2.me/theorems/eedb7da4-39a4-4480-844d-d128211c6a3f
-- title:
--   Galois Descent: base Change eq span image
-- statement:
--   The Galois Descent construction uses the base Change eq span image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsOneTmulOfForallFixed.lean#L257-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/ExistsOneTmulOfForallFixed.lean#L257-L259

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_ExistsOneTmulOfForallFixed
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct Module
open GlobalTheory GlobalTheory.GaloisDescent
variable {K L V G : Type*} [Field K] [Field L] [Algebra K L] [AddCommGroup V] [Module K V]

theorem GlobalTheory.GaloisDescent.baseChange_eq_span_image (N : Submodule K V) :
    N.baseChange L = Submodule.span L (TensorProduct.mk K L V 1 '' N) := by sorry
