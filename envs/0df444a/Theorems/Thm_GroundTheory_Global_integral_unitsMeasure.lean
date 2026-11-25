-- Prove2me | Theorems.Thm_GroundTheory_Global_integral_unitsMeasure
-- name    : GroundTheory.Global.integral_unitsMeasure
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:13:33.95315+00:00
-- url     : https://prove2.me/theorems/27e0c852-5061-43c8-aadd-a8bc2f265a65
-- title:
--   Global: integral units Measure
-- statement:
--   The Global construction uses the integral units Measure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/EulerFactorsArch.lean#L20-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/TateThesis/EulerFactorsArch.lean#L20-L34

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_HeckeChar
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_IdeleMeasure
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_ArchCharsUnitary
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_Gaussian
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_GaussianComplex
import Definitions.Def_GroundTheory_GlobalFields_TateThesis_EulerFactorsArch
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open NumberField InfinitePlace InfinitePlace.Completion MeasureTheory Complex ComplexConjugate
open scoped Real
open GroundTheory GroundTheory.Global
noncomputable section
variable {F : Type*} [NormedField F] [LocallyCompactSpace F] [SecondCountableTopology F]
  [MeasurableSpace F] [BorelSpace F]

theorem GroundTheory.Global.integral_unitsMeasure (μ : Measure F) (hμ : μ {0} = 0) (m : ℕ) (g : F → ℂ) :
    ∫ a : Fˣ, g a ∂unitsMeasure μ m = ∫ x, ((‖x‖ ^ m)⁻¹ : ℝ) • g x ∂μ := by sorry
