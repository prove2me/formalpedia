-- Prove2me | Theorems.Thm_Kyprianou_Ch03_supInfDuality_pairLawOfVectorLaw
-- name    : Kyprianou.Ch03.supInfDuality_pairLawOfVectorLaw
-- status  : Open
-- author  : @WillR
-- created : 2026-11-24T11:02:17.517904+00:00
-- url     : https://prove2.me/theorems/2948e94e-47c5-4d10-b5dc-c2ef59f3af85
-- title:
--   Measurable extrema-pair transfer on a reflection-invariant grid
-- statement:
--   Apply the measurable map taking the maximum minus final coordinate and the maximum to both equal vector laws; grid reflection and elementary extrema algebra give the two pairs.
-- source:
--   Kyprianou (2006), Lemma 3.5; uniform-grid reversal proof.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
set_option autoImplicit false

theorem Kyprianou.Ch03.supInfDuality_pairLawOfVectorLaw
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (X : NNReal → Omega → ℝ) (hX : IsLevyProcess X P)
    (t : NNReal) (m : ℕ) (q : Fin (m + 1) → NNReal)
    (hend : q (Fin.last m) = t)
    (href : Set.range (fun i => t - q i) = Set.range q)
    (hLaw : P.map (fun ω : Omega => fun i => X (t - q i) ω - X t ω) =
      P.map (fun ω : Omega => fun i => -X (q i) ω)) :
    P.map (fun ω : Omega =>
      let a := sSup (Set.range (fun i => X (q i) ω))
      (a, a - X t ω)) =
    P.map (fun ω : Omega =>
      let b := sInf (Set.range (fun i => X (q i) ω))
      (X t ω - b, -b)) := by sorry
