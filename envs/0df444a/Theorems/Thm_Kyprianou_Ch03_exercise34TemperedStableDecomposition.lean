-- Prove2me | Theorems.Thm_Kyprianou_Ch03_exercise34TemperedStableDecomposition
-- name    : Kyprianou.Ch03.exercise34TemperedStableDecomposition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T09:51:52.996313+00:00
-- url     : https://prove2.me/theorems/48e9d5ac-311f-4266-802f-cb4233689e8e
-- title:
--   Exercise 3.4: decomposition and component classification of tempered stable laws
-- statement:
--   Construct independent positive-jump Lévy components of a generalised tempered stable process and recover X as their difference in law. Includes finite jump intensity for negative indices, with the zero, unit and other stable-index regimes determined by the common tempered power-tail density; further classification identities can be split into companion lemmas.
-- source:
--   Kyprianou (2006), Exercise 3.4(i)-(iv), p. 84; solution p. 314.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
import Definitions.Def_Kyprianou_Ch01_LevyTripletExponent
import Definitions.Def_Kyprianou_Ch03_TemperedStableMeasure
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch03

theorem exercise34TemperedStableDecomposition
{Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ)
    (hX : ProbabilityTheory.IsLevyProcess X P)
    (T : ProbabilityTheory.LevyKhintchineTriple)
    (hLK : ∀ (t : NNReal) (xi : ℝ),
      charFun (P.map (X t)) xi =
        Complex.exp (((t : ℝ) : ℂ) *
          Kyprianou.Ch01.levyTripleExponent T xi))
    (cp ap gp cm am gm : ℝ)
    (hcp : 0 < cp) (hcm : 0 < cm)
    (hap : ap < 2) (ham : am < 2)
    (hgp : 0 < gp) (hgm : 0 < gm)
    (hGaussian : T.gaussianVariance = 0)
    (hMeasure : T.levyMeasure =
      temperedStableSignedMeasure cp ap gp cm am gm) :
    ∃ (OmegaP OmegaM : Type)
      (mP : MeasurableSpace OmegaP) (mM : MeasurableSpace OmegaM),
      letI : MeasurableSpace OmegaP := mP
      letI : MeasurableSpace OmegaM := mM
      ∃ (PP : Measure OmegaP) (PM : Measure OmegaM),
        ∃ (hPP : IsProbabilityMeasure PP) (hPM : IsProbabilityMeasure PM),
        letI : IsProbabilityMeasure PP := hPP
        letI : IsProbabilityMeasure PM := hPM
        ∃ (XP : NNReal → OmegaP → ℝ) (XM : NNReal → OmegaM → ℝ)
          (TP TM : ProbabilityTheory.LevyKhintchineTriple),
          ProbabilityTheory.IsLevyProcess XP PP ∧
          ProbabilityTheory.IsLevyProcess XM PM ∧
          TP.gaussianVariance = 0 ∧ TM.gaussianVariance = 0 ∧
          TP.levyMeasure = temperedStablePositiveMeasure cp ap gp ∧
          TM.levyMeasure = temperedStablePositiveMeasure cm am gm ∧
          (∀ (t : NNReal) (xi : ℝ),
            charFun (PP.map (XP t)) xi =
              Complex.exp (((t : ℝ) : ℂ) *
                Kyprianou.Ch01.levyTripleExponent TP xi)) ∧
          (∀ (t : NNReal) (xi : ℝ),
            charFun (PM.map (XM t)) xi =
              Complex.exp (((t : ℝ) : ℂ) *
                Kyprianou.Ch01.levyTripleExponent TM xi)) ∧
          (∀ t : NNReal,
            Measure.map
              (fun pair : OmegaP × OmegaM => XP t pair.1 - XM t pair.2)
              (PP.prod PM) =
            P.map (X t)) ∧
          (ap < 0 → temperedStablePositiveMeasure cp ap gp Set.univ < ⊤) ∧
          (am < 0 → temperedStablePositiveMeasure cm am gm Set.univ < ⊤) ∧
          (∀ alpha c gamma : ℝ, 0 < c → 0 < gamma →
            temperedStablePositiveMeasure c alpha gamma =
              (temperedStablePositiveMeasure c alpha 0).withDensity
                (fun x => ENNReal.ofReal (Real.exp (-gamma * x)))) := by
  sorry

end Kyprianou.Ch03
