-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmFiniteVectorShiftCountLawV1
-- name    : Kyprianou.Ch02.prmFiniteVectorShiftCountLawV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T11:52:02.996886+00:00
-- url     : https://prove2.me/theorems/f8121593-3cd5-45f4-924a-9c1bd361b08e
-- title:
--   Finite-vector joint stationary law of disjoint Poisson marked-window counts
-- statement:
--   For any finite family of pairwise disjoint measurable mark cells with finite ν intensity, the joint vector of Poisson random-measure counts on the shifted time window (s,s+t] has the same law as on (0,t]. Combine N.independent_disjoint, iIndepFun_iff_map_fun_eq_pi_map, and the already remotely Proved source-exact one-cell shifted Poisson window-count law. This finite-dimensional stationarity is a genuine prerequisite for weighted simple-mark compound-Poisson increment laws.
-- source:
--   Kyprianou (2006) Chapter 2 finite-region compound Poisson stationary increments; LevyStochCalc/Poisson/RandomMeasure.lean and Proved prmTimeShiftedWindowCountLawV1.

import Mathlib
import Definitions.Def_LevyStochCalc_Poisson_Atomic_F000
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmFiniteVectorShiftCountLawV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (n : ℕ) (C : Fin n → Set ℝ)
    (hC : ∀ i, MeasurableSet (C i))
    (hfinite : ∀ i, ν (C i) < ⊤)
    (hdisj : Pairwise (fun i j => Disjoint (C i) (C j)))
    (s t : ℝ≥0) :
    P.map (fun (ω : Ω) (i : Fin n) =>
      N.N ω (Set.Ioc (s : ℝ) ((s + t : ℝ≥0) : ℝ) ×ˢ C i)) =
    P.map (fun (ω : Ω) (i : Fin n) =>
      N.N ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ C i)) := by sorry
