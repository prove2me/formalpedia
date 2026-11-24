-- Prove2me | Theorems.Thm_GroundTheory_Global_SUnit_finrank_range_valuationVector
-- name    : GroundTheory.Global.SUnit.finrank_range_valuationVector
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:39:20.272709+00:00
-- url     : https://prove2.me/theorems/27b1c973-0da7-4cbb-ae35-20d8d1aefb86
-- title:
--   SUnit: finrank range valuation Vector
-- statement:
--   The SUnit construction uses the finrank range valuation Vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SUnits.lean#L127-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SUnits.lean#L127-L145

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_SUnitsKernel
import Definitions.Def_GroundTheory_GlobalFields_SUnits
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Module
open scoped NumberField nonZeroDivisors
noncomputable section
variable {K : Type*} [Field K] [NumberField K]
open GroundTheory.Global.SUnit
variable (S : Set (HeightOneSpectrum (𝓞 K)))
variable [Finite S]

theorem GroundTheory.Global.SUnit.finrank_range_valuationVector :
    finrank ℤ (LinearMap.range (valuationVector S)) = Nat.card S := by sorry
