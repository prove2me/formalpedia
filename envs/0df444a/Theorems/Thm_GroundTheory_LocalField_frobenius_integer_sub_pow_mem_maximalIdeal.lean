-- Prove2me | Theorems.Thm_GroundTheory_LocalField_frobenius_integer_sub_pow_mem_maximalIdeal
-- name    : GroundTheory.LocalField.frobenius_integer_sub_pow_mem_maximalIdeal
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T09:44:30.046864+00:00
-- url     : https://prove2.me/theorems/9629775c-a6fe-410b-845b-61aa7f5a0972
-- title:
--   Local Field: frobenius integer sub pow mem maximal Ideal
-- statement:
--   The Local Field construction uses the frobenius integer sub pow mem maximal Ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/MaximalUnramifiedIntegers.lean#L284-L318
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/MaximalUnramifiedIntegers.lean#L284-L318

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
variable [IsGalois K Ω]

theorem GroundTheory.LocalField.frobenius_integer_sub_pow_mem_maximalIdeal (x : 𝒪[𝔼]) :
    integerAlgEquivOfIsAlgebraic K 𝔼 (maximalUnramifiedExtensionFrobenius K Ω) x -
      x ^ Nat.card 𝓀[K] ∈ 𝓂[𝔼] := by sorry
