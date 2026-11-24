-- Prove2me | Theorems.Thm_GroundTheory_LocalField_vlt_map_iff
-- name    : GroundTheory.LocalField.vlt_map_iff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:44:58.957188+00:00
-- url     : https://prove2.me/theorems/dd03728b-1089-4a5b-96aa-5c66fbba4fce
-- title:
--   Local Field: vlt map iff
-- statement:
--   The Local Field construction uses the vlt map iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Uniqueness.lean#L119-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Uniqueness.lean#L119-L120

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_Uniqueness
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel Topology Filter
variable {K L M : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
  [Field M] [ValuativeRel M] [TopologicalSpace M] [IsNonarchimedeanLocalField M]
  [Algebra K M] [ValuativeExtension K M]

theorem GroundTheory.LocalField.vlt_map_iff (f : L →ₐ[K] M) (x y : L) : f x <ᵥ f y ↔ x <ᵥ y := by sorry
