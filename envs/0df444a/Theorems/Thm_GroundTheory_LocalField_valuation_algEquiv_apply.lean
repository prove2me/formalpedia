-- Prove2me | Theorems.Thm_GroundTheory_LocalField_valuation_algEquiv_apply
-- name    : GroundTheory.LocalField.valuation_algEquiv_apply
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:20:12.212541+00:00
-- url     : https://prove2.me/theorems/715b59ce-d8dc-4bc3-ab97-dde24a6b5cc0
-- title:
--   Local Field: valuation alg Equiv apply
-- statement:
--   The Local Field construction uses the valuation alg Equiv apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Uniqueness.lean#L232-L251
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Uniqueness.lean#L232-L251

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
variable (K L)

theorem GroundTheory.LocalField.valuation_algEquiv_apply (σ : L ≃ₐ[K] L) (x : L) : valuation L (σ x) = valuation L x := by sorry
