-- Prove2me | Theorems.Thm_GroundTheory_LocalField_partialNorm_add_orderOf
-- name    : GroundTheory.LocalField.partialNorm_add_orderOf
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:45:07.680139+00:00
-- url     : https://prove2.me/theorems/77416dec-327a-4ab1-8ea5-b5b7c1f0bd74
-- title:
--   Local Field: partial Norm add order Of
-- statement:
--   The Local Field construction uses the partial Norm add order Of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HilbertCyclic.lean#L46-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HilbertCyclic.lean#L46-L48

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
variable {σ}
variable (hσ : ∀ g, g ∈ Subgroup.zpowers σ) {x} (hx : tateNorm (L ≃ₐ[K] L) Lˣ x = 1)
include hσ hx

theorem GroundTheory.LocalField.partialNorm_add_orderOf (m : ℕ) :
    partialNorm σ x (m + orderOf σ) = partialNorm σ x m := by sorry
