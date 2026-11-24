-- Prove2me | Theorems.Thm_Kyprianou_Ch03_momentFourierCharacterIntegrableV1
-- name    : Kyprianou.Ch03.momentFourierCharacterIntegrableV1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T13:16:17.806302+00:00
-- url     : https://prove2.me/theorems/74c09bc8-4518-4772-9427-4dd2a35528bf
-- title:
--   Integrability of the Fourier character for finite real measures
-- statement:
--   The Fourier character is measurable and has norm one, so it is dominated by the integrable constant one.
-- source:
--   Kyprianou (2006), Theorems 3.6 and 3.8; decomposition of compound-Poisson characteristic function and compensated exponential kernel.

import Mathlib
import Definitions.Def_KSATSingleFlip_Connect_SoftField
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
open MeasureTheory ProbabilityTheory Set Filter Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.momentFourierCharacterIntegrableV1
    (mu : Measure Real) [IsFiniteMeasure mu] (xi : Real) :
    Integrable (fun x : Real => Complex.exp ((xi : ℂ) * (x : ℂ) * Complex.I)) mu := by sorry
