-- Prove2me | Theorems.Thm_GroundTheory_LocalField_partialNorm_add
-- name    : GroundTheory.LocalField.partialNorm_add
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:00:11.921638+00:00
-- url     : https://prove2.me/theorems/b852b48c-cbab-4cde-a8c7-21e63ae127f9
-- title:
--   Local Field: partial Norm add
-- statement:
--   The Local Field construction uses the partial Norm add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HilbertCyclic.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HilbertCyclic.lean#L18-L21

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_CompleteTrivial
import Definitions.Def_GroundTheory_LocalFields_HilbertCyclic
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField
open Finset
variable {K L : Type*} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
variable (σ : L ≃ₐ[K] L) (x : Lˣ)
omit [FiniteDimensional K L]

theorem GroundTheory.LocalField.partialNorm_add (a b : ℕ) :
    partialNorm σ x (a + b) = partialNorm σ x a * (σ ^ a) • partialNorm σ x b := by sorry
