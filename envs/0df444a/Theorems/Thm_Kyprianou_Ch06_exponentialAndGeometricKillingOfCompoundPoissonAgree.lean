-- Prove2me | Theorems.Thm_Kyprianou_Ch06_exponentialAndGeometricKillingOfCompoundPoissonAgree
-- name    : Kyprianou.Ch06.exponentialAndGeometricKillingOfCompoundPoissonAgree
-- status  : Open
-- author  : @WillR
-- created : 2026-11-15T22:12:56.823743+00:00
-- url     : https://prove2.me/theorems/0e80409e-9014-4931-8cdf-1affb202264c
-- title:
--   Exercise 6.3: exponential killing equals geometric jump killing
-- statement:
--   For λ>0 and 0<ρ≤1, show equality in all finite-dimensional laws between a compound Poisson cumulative-jump process with rate λρ killed at an independent time of exponential rate λ(1−ρ), and a rate-λ cumulative-jump process killed after an independent geometric number of completed jumps. The geometric law has mass (1−ρ)ρ^n on nonnegative n. When ρ=1 the slow killing time and fast geometric count are both infinite almost surely, so neither construction is killed. The formal hypotheses specify the Poisson count increments, matching joint mark laws, and the independence of counts, marks and killing needed for this full path-law identity.
-- source:
--   Kyprianou (2006), Exercise 6.3, printed p. 175; two-up PDF p. 93.

import Mathlib
import Definitions.Def_Kyprianou_Ch06_RegularityAtFirstEntrance
open MeasureTheory Filter
open scoped NNReal ENNReal
set_option autoImplicit false

namespace Kyprianou.Ch06

/-- Exercise 6.3, full path-law formulation. The first process has
Poisson jump rate lambda*rho and independent exponential killing
at rate lambda*(1-rho); the second has Poisson rate lambda and a
geometric number N of jumps before its (N+1)st event kills it.
The geometric count is on {0,1,2,...} with law (1-rho)*rho^n. -/
theorem exponentialAndGeometricKillingOfCompoundPoissonAgree
    (rho lambda : Real)
    (hRho : 0 < rho ∧ rho ≤ 1)
    (hLambda : 0 < lambda)
    {Omega : Type} [MeasurableSpace Omega]
    (P : Measure Omega) [IsProbabilityMeasure P]
    (Nslow Nfast : NNReal → Omega → Nat)
    (Yslow Yfast : Nat → Omega → NNReal)
    (killTime : Omega → WithTop NNReal)
    (geometricCount : Omega → WithTop Nat)
    (hSlow : ∀ t : NNReal, ∀ n : Nat,
      P {omega | Nslow t omega = n} =
        ProbabilityTheory.poissonMeasure
          (ENNReal.ofReal (lambda * rho * (t : Real))).toNNReal {n})
    (hFast : ∀ t : NNReal, ∀ n : Nat,
      P {omega | Nfast t omega = n} =
        ProbabilityTheory.poissonMeasure
          (ENNReal.ofReal (lambda * (t : Real))).toNNReal {n})
    (hKill : ∀ t : NNReal,
      P {omega | (t : WithTop NNReal) < killTime omega} =
        ENNReal.ofReal (Real.exp (-(lambda * (1-rho)) * (t : Real))))
    (hGeom : ∀ n : Nat,
      P {omega | geometricCount omega = (n : WithTop Nat)} =
        ENNReal.ofReal ((1-rho) * rho ^ n))
    (hGeomInfinity :
      P {omega | geometricCount omega = ⊤} =
        if rho = 1 then 1 else 0)
    (hMarkLaw : ∀ k : Nat, ∀ A : Fin k → Set NNReal,
      (∀ i, MeasurableSet (A i)) →
      P {omega | ∀ i : Fin k, Yslow i omega ∈ A i} =
        P {omega | ∀ i : Fin k, Yfast i omega ∈ A i})
    (hSlowCountIncrements : ∀ (k : Nat)
      (times : Fin (k + 1) → NNReal) (counts : Fin k → Nat),
      StrictMono times →
      P {omega | ∀ i : Fin k,
        Nslow (times i.succ) omega -
          Nslow (times i.castSucc) omega = counts i} =
        ∏ i : Fin k,
          ProbabilityTheory.poissonMeasure
            (ENNReal.ofReal (lambda * rho *
              (((times i.succ - times i.castSucc) : NNReal) : Real))).toNNReal
              {counts i})
    (hFastCountIncrements : ∀ (k : Nat)
      (times : Fin (k + 1) → NNReal) (counts : Fin k → Nat),
      StrictMono times →
      P {omega | ∀ i : Fin k,
        Nfast (times i.succ) omega -
          Nfast (times i.castSucc) omega = counts i} =
        ∏ i : Fin k,
          ProbabilityTheory.poissonMeasure
            (ENNReal.ofReal (lambda *
              (((times i.succ - times i.castSucc) : NNReal) : Real))).toNNReal
              {counts i})
    (hSlowIndependence : ∀ (m k : Nat)
      (times : Fin m → NNReal) (counts : Fin m → Nat)
      (u : NNReal) (A : Fin k → Set NNReal),
      (∀ i, MeasurableSet (A i)) →
      P {omega | (∀ j : Fin m,
          Nslow (times j) omega = counts j) ∧
        (u : WithTop NNReal) < killTime omega ∧
        (∀ i : Fin k, Yslow i omega ∈ A i)} =
        P {omega | ∀ j : Fin m,
          Nslow (times j) omega = counts j} *
        P {omega | (u : WithTop NNReal) < killTime omega} *
        P {omega | ∀ i : Fin k, Yslow i omega ∈ A i})
    (hFastIndependence : ∀ (m k : Nat)
      (times : Fin m → NNReal) (counts : Fin m → Nat)
      (z : WithTop Nat) (A : Fin k → Set NNReal),
      (∀ i, MeasurableSet (A i)) →
      P {omega | (∀ j : Fin m,
          Nfast (times j) omega = counts j) ∧
        geometricCount omega = z ∧
        (∀ i : Fin k, Yfast i omega ∈ A i)} =
        P {omega | ∀ j : Fin m,
          Nfast (times j) omega = counts j} *
        P {omega | geometricCount omega = z} *
        P {omega | ∀ i : Fin k, Yfast i omega ∈ A i}) :
    ∀ (m : Nat) (times : Fin m → NNReal)
      (A : Fin m → Set (Option NNReal)),
      (∀ i, MeasurableSet (A i)) →
      P {omega | ∀ i : Fin m,
        (if (times i : WithTop NNReal) < killTime omega then
          some (∑ j ∈ Finset.range (Nslow (times i) omega),
            Yslow j omega) else none) ∈ A i} =
      P {omega | ∀ i : Fin m,
        (if (Nfast (times i) omega : WithTop Nat) ≤ geometricCount omega then
          some (∑ j ∈ Finset.range (Nfast (times i) omega),
            Yfast j omega) else none) ∈ A i} := by
  sorry

end Kyprianou.Ch06
