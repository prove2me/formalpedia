-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmKLSFiniteVectorShiftCountLawV1
-- name    : Kyprianou.Ch02.prmKLSFiniteVectorShiftCountLawV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T18:11:26.636255+00:00
-- url     : https://prove2.me/theorems/e423f0e8-ceac-434b-a976-e0f3f3d7cdfb
-- title:
--   Joint time-shift law for disjoint KLS Poisson count vectors
-- statement:
--   Exact adaptation of proved Kyprianou.Ch02.prmFiniteVectorShiftCountLawV1 source to KLS provider, using N.independent_disjoint, iIndepFun_iff_map_fun_eq_pi_map, and the KLS scalar time-shift lemma above. Required by finite simple sum stationarity and Eq 2.3.
-- source:
--   Kyprianou (2006) Chapter 2 Eq. (2.3); KLS-modular PoissonRandomMeasure provider.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmKLSFiniteVectorShiftCountLawV1
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
