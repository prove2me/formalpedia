-- Prove2me | Theorems.Thm_GroundTheory_Global_SUnit_valuationVector_comp_placeUnitsMap
-- name    : GroundTheory.Global.SUnit.valuationVector_comp_placeUnitsMap
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:28:11.599269+00:00
-- url     : https://prove2.me/theorems/e3e60a73-7f90-4770-952f-eae4f563acf0
-- title:
--   SUnit: valuation Vector comp place Units Map
-- statement:
--   The SUnit construction uses the valuation Vector comp place Units Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SUnits.lean#L119-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SUnits.lean#L119-L125

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

theorem GroundTheory.Global.SUnit.valuationVector_comp_placeUnitsMap :
    valuationVector S ∘ₗ placeUnitsMap S = (-(classNumber K : ℤ)) • LinearMap.id := by sorry
