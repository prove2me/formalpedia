-- Prove2me | Theorems.Thm_GroundTheory_LocalField_maximalIdeal_ne_bot
-- name    : GroundTheory.LocalField.maximalIdeal_ne_bot
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:19:43.844261+00:00
-- url     : https://prove2.me/theorems/90fde339-f75c-414e-8117-8bcfce706b5d
-- title:
--   Local Field: maximal Ideal ne bot
-- statement:
--   The Local Field construction uses the maximal Ideal ne bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Integers.lean#L130-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Integers.lean#L130-L131

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_Interface
import Definitions.Def_GroundTheory_LocalFields_FiniteExtension
import Definitions.Def_GroundTheory_LocalFields_Integers
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
open ValuativeRel
variable (K L : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L]
variable [FiniteDimensional K L]

theorem GroundTheory.LocalField.maximalIdeal_ne_bot : IsLocalRing.maximalIdeal 𝒪[K] ≠ ⊥ := by sorry
