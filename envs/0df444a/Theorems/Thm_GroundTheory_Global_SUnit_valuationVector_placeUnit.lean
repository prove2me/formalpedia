-- Prove2me | Theorems.Thm_GroundTheory_Global_SUnit_valuationVector_placeUnit
-- name    : GroundTheory.Global.SUnit.valuationVector_placeUnit
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:39:57.363031+00:00
-- url     : https://prove2.me/theorems/e3176708-68b0-4a56-8762-38b0ec116918
-- title:
--   SUnit: valuation Vector place Unit
-- statement:
--   The SUnit construction uses the valuation Vector place Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SUnits.lean#L72-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/SUnits.lean#L72-L80

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
open scoped Classical

theorem GroundTheory.Global.SUnit.valuationVector_placeUnit (v : S) :
    valuationVector S (Additive.ofMul ⟨placeUnit v.1, placeUnit_mem S v.2⟩) =
      Pi.single v (-(classNumber K : ℤ)) := by sorry
