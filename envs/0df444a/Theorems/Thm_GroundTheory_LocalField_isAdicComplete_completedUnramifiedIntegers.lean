-- Prove2me | Theorems.Thm_GroundTheory_LocalField_isAdicComplete_completedUnramifiedIntegers
-- name    : GroundTheory.LocalField.isAdicComplete_completedUnramifiedIntegers
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T13:00:21.76332+00:00
-- url     : https://prove2.me/theorems/b26e8a3b-b7d3-5107-a2ac-1e67b7e5e81d
-- title:
--   Local Field: is Adic Complete completed Unramified Integers
-- statement:
--   The Local Field construction uses the is Adic Complete completed Unramified Integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompletedUnramified.lean#L397-L398
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/CompletedUnramified.lean#L397-L398

import Mathlib
import Definitions.Def_GroundTheory_LocalFields_MaximalUnramifiedIntegers
import Definitions.Def_GroundTheory_PowerSubgroups_CountableNeighbourhoods_UnitMulPowAdic
import Definitions.Def_GroundTheory_LocalFields_CompletedUnramified
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
open IsLocalRing ValuativeRel
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
  (Ω : Type*) [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] [HasUnramifiedRoots K Ω]
local notation "𝔼" => maximalUnramifiedExtension K Ω
local notation "𝔹" => CompletedUnramifiedIntegers K Ω

theorem GroundTheory.LocalField.isAdicComplete_completedUnramifiedIntegers : IsAdicComplete (maximalIdeal 𝔹) 𝔹 := by sorry
