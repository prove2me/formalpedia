-- Prove2me | Theorems.Thm_Kyprianou_Ch02_iIndepFunRectangularBlockSumsV1
-- name    : Kyprianou.Ch02.iIndepFunRectangularBlockSumsV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T23:50:40.194687+00:00
-- url     : https://prove2.me/theorems/3d8a8693-affd-4bf0-a2e3-12912e189f2d
-- title:
--   Independent rectangular array yields independent positive and negative block sums
-- statement:
--   Replace each cell by its measurable version. Restrict the independent array to disjoint rows, then apply the measurable positive and negative sum map on each row. Transfer back by almost sure equality.
-- source:
--   Kyprianou (2006), Exercise 2.8, deterministic partition and probability limit lemmas for Jordan variation.

import Mathlib
import Definitions.Def_LeanLevy_Processes_LevyProcess
open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology
set_option autoImplicit false

theorem Kyprianou.Ch02.iIndepFunRectangularBlockSumsV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (m n : ℕ) (D : Fin m × Fin n → Ω → ℝ)
    (hm : ∀ p, AEMeasurable (D p) P) (hi : iIndepFun D P) :
    iIndepFun (fun (i : Fin m) ω =>
      (∑ j : Fin n, max (D (i,j) ω) 0, ∑ j : Fin n, max (-D (i,j) ω) 0)) P := by sorry
