-- Prove2me | Theorems.Thm_Kyprianou_Ch02_prmKLSFiniteDisjointWeightedCountCharV1
-- name    : Kyprianou.Ch02.prmKLSFiniteDisjointWeightedCountCharV1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-23T21:18:50.231798+00:00
-- url     : https://prove2.me/theorems/bd1e5fc2-d6e9-47ce-b49b-362371852302
-- title:
--   Joint characteristic exponent of finite independent weighted Poisson mark-cell counts
-- statement:
--   For pairwise disjoint measurable finite-intensity mark cells C i, use N.independent_disjoint to show independent Poisson random counts. Apply ProbabilityTheory.iIndepFun.comp to the measurable weighted-real-toReal counts and ProbabilityTheory.iIndepFun.charFun_map_finset_sum_eq_prod. Each scalar factor is given by the Proved Kyprianou.Ch02.finiteRegionPoissonCountCharacteristicV1 with u=ξ*w i. Re-express referenceIntensity ν((0,t]×C i)=(t)*ν(C i) and use Complex.exp_sum. This is a reusable finite-index child for Kyprianou.Ch02.prmKLSFiniteSimpleFibreWeightedCountCharV1, itself connected by accepted sketch to the Chapter 2 Eq 2.3 optional simple-mark exponent theorem.
-- source:
--   Kyprianou (2006) Chapter 2, compound Poisson characteristic exponent.

import Mathlib
import Definitions.Def_KLSModular_LevyStochCalc_Poisson_RandomMeasure
open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal
set_option autoImplicit false

theorem Kyprianou.Ch02.prmKLSFiniteDisjointWeightedCountCharV1
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (ν : Measure ℝ) [SigmaFinite ν]
    (N : LevyStochCalc.Poisson.PoissonRandomMeasure.{0, 0, 0} P ν)
    (n : ℕ) (C : Fin n → Set ℝ)
    (hC : ∀ i, MeasurableSet (C i))
    (hfinite : ∀ i, ν (C i) < ⊤)
    (hdisj : Pairwise (fun i j => Disjoint (C i) (C j)))
    (w : Fin n → ℝ) (t : ℝ≥0) (ξ : ℝ) :
    charFun (P.map (fun (ω : Ω) =>
      ∑ i : Fin n, w i *
        (N.N ω (Set.Ioc (0 : ℝ) (t : ℝ) ×ˢ C i)).toReal)) ξ =
      Complex.exp (∑ i : Fin n,
        ((((t : ℝ) * (ν (C i)).toReal : ℝ) : ℂ) *
          (Complex.exp (Complex.I * (((ξ * w i : ℝ) : ℂ))) - 1))) := by sorry
