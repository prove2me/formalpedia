-- Prove2me | Theorems.Thm_GroundTheory_LocalField_isSolvable_algEquiv
-- name    : GroundTheory.LocalField.isSolvable_algEquiv
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:46:52.320826+00:00
-- url     : https://prove2.me/theorems/1927c038-e0a8-4e3e-9865-df87828b7ebc
-- title:
--   Local Field: is Solvable alg Equiv
-- statement:
--   The Local Field construction uses the is Solvable alg Equiv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/RamificationStructure.lean#L149-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/RamificationStructure.lean#L149-L156

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_RamificationUnits
import Definitions.Def_GroundTheory_LocalFields_RamificationStructure
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
open ValuativeRel IsLocalRing
variable {K L : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L] [FiniteDimensional K L]
variable (K L)

theorem GroundTheory.LocalField.isSolvable_algEquiv : Group.IsSolvable (L ≃ₐ[K] L) := by sorry
