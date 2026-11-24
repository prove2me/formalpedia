-- Prove2me | Theorems.Thm_Kyprianou_Ch03_negativeLevyLaplaceFromTripleV1
-- name    : Kyprianou.Ch03.negativeLevyLaplaceFromTripleV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-24T19:00:38.036577+00:00
-- url     : https://prove2.me/theorems/5a4507e9-71cf-422c-8e88-ed10e3fed013
-- title:
--   Nonpositive-support Lévy triplet gives the real Laplace transform
-- statement:
--   Use the Lévy–Khintchine exponential moment theorem for a jump measure carried by negative reals, with the identical truncation convention; transfer across indistinguishable coordinates.
-- source:
--   Kyprianou (2006), Chapters 2–3; reduction of 063b9d7c-87f6-432a-91c5-8ca8556a76f0.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_CompletedNaturalFiltration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Filter Set Topology
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.negativeLevyLaplaceFromTripleV1
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : ∀ (t : NNReal) (xi : ℝ),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : ℝ) : ℂ) *
          Kyprianou.Ch01.levyTripleExponent T xi))
    (hNegative : T.levyMeasure (Set.Ici (0 : ℝ)) = 0)
    (Y : NNReal → Omega → ℝ)
    (hY : ∀ᵐ omega ∂P, ∀ t : NNReal, Y t omega = X t omega)
    (hMeas : ∀ t, Measurable (Y t)) :
    ∀ (t : NNReal) (theta : ℝ), 0 ≤ theta →
      Integrable (fun omega => Real.exp (theta * Y t omega)) P ∧
        ∫ omega, Real.exp (theta * Y t omega) ∂P =
          Real.exp ((t : ℝ) * AvramDividend.Classical.laplaceExponent
            T.drift (Real.sqrt (T.gaussianVariance : ℝ)) T.levyMeasure theta) := by
  sorry
