-- Prove2me | Theorems.Thm_GroundTheory_LocalField_map_maximalIdeal_integer
-- name    : GroundTheory.LocalField.map_maximalIdeal_integer
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:43:56.802294+00:00
-- url     : https://prove2.me/theorems/cd1113a9-b504-43d0-bf24-240a0fd0ba1f
-- title:
--   Local Field: map maximal Ideal integer
-- statement:
--   The Local Field construction uses the map maximal Ideal integer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/MaximalUnramifiedIntegers.lean#L183-L186
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/MaximalUnramifiedIntegers.lean#L183-L186

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramified
import Definitions.Def_GroundTheory_LocalFields_SeparableClosureValuation
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramifiedIntegers
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open GroundTheory GroundTheory.LocalField
open ValuativeRel IsLocalRing
variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [HasUnramifiedRoots K Ω]
local notation "𝔼" => maximalUnramifiedExtension K Ω

theorem GroundTheory.LocalField.map_maximalIdeal_integer : (𝓂[K]).map (algebraMap 𝒪[K] 𝒪[𝔼]) = 𝓂[𝔼] := by sorry
