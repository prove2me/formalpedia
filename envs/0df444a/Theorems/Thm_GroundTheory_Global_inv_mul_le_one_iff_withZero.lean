-- Prove2me | Theorems.Thm_GroundTheory_Global_inv_mul_le_one_iff_withZero
-- name    : GroundTheory.Global.inv_mul_le_one_iff_withZero
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T03:14:09.372565+00:00
-- url     : https://prove2.me/theorems/bb54258e-2855-5f94-a291-8a3e5db58d34
-- title:
--   Global: inv mul le one iff with Zero
-- statement:
--   The Global construction uses the inv mul le one iff with Zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleIdealMeasure.lean#L43-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/AdeleIdealMeasure.lean#L43-L51

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_FiniteAdeleScaling
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleScaling
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_AdeleIdealMeasure
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
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum MeasureTheory Measure WithZero
open scoped NumberField.AdeleRing ENNReal NNReal Pointwise nonZeroDivisors
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

theorem GroundTheory.Global.inv_mul_le_one_iff_withZero {b c : ℤᵐ⁰} (hc : c ≠ 0) : c⁻¹ * b ≤ 1 ↔ b ≤ c := by sorry
