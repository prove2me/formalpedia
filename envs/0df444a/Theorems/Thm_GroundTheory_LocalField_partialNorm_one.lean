-- Prove2me | Theorems.Thm_GroundTheory_LocalField_partialNorm_one
-- name    : GroundTheory.LocalField.partialNorm_one
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T23:44:57.101845+00:00
-- url     : https://prove2.me/theorems/88cde325-ca5f-4aca-a70c-6fc14f74247c
-- title:
--   Local Field: partial Norm one
-- statement:
--   The Local Field construction uses the partial Norm one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HilbertCyclic.lean#L24-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/HilbertCyclic.lean#L24-L25

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

theorem GroundTheory.LocalField.partialNorm_one : partialNorm σ x 1 = x := by sorry
