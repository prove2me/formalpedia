-- Prove2me | Theorems.Thm_GroundTheory_LocalField_map_maximalIdeal
-- name    : GroundTheory.LocalField.map_maximalIdeal
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:16:52.002319+00:00
-- url     : https://prove2.me/theorems/984a0e77-2c7e-4e10-bb2c-8d7e2fd24d12
-- title:
--   Local Field: map maximal Ideal
-- statement:
--   The Local Field construction uses the map maximal Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Integers.lean#L133-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/Integers.lean#L133-L146

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

theorem GroundTheory.LocalField.map_maximalIdeal :
    (IsLocalRing.maximalIdeal 𝒪[K]).map (algebraMap 𝒪[K] 𝒪[L]) =
      IsLocalRing.maximalIdeal 𝒪[L] ^ ramificationIndex K L := by sorry
