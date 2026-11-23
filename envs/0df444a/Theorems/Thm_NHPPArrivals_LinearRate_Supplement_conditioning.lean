-- Prove2me | Theorems.Thm_NHPPArrivals_LinearRate_Supplement_conditioning
-- name    : NHPPArrivals.LinearRate.Supplement.conditioning
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T12:08:24.94164+00:00
-- url     : https://prove2.me/theorems/b08f2fdd-a825-4aad-a441-70e120d6f146
-- title:
--   THEOREM 1 — NHPP conditioning, full joint law, cdf, density and scale invariance
-- statement:
--   Let $N$ be an NHPP of rate $c\lambda$ on $[0,T]$, for any $c>0$, under §3.2's standing rate assumptions. Set $\mu=\mu_{\lambda,T}$, the scaled published one-arrival law. Then $\Lambda(T)>0$, $\mu$ is a probability measure, and
--   $$\mu(({-\infty},t])=F(t)=\frac{\Lambda(tT)}{\Lambda(T)},\qquad \frac{d\mu}{dt}=f(t)=\frac{T\lambda(tT)}{\Lambda(T)}\quad(0\le t\le1),$$
--   with density zero outside $[0,1]$. For every $n\ge0$, $P(N(T)=n)>0$ and
--   $$\mathcal L((X_1/T,\ldots,X_n/T)\mid N(T)=n)=\operatorname{sort}_*(\mu^{\otimes n}).$$
--   The measure $\mu$, cdf $F$ and density $f$ are unchanged when $\lambda$ is multiplied by any positive constant. This is a joint vector law: ordered coordinates are not asserted independent.
--
--   This result identifies the observations used by all subsequent statistical limits.
--
--   Differences from the source:
--   - encoding: An NHPP with the standing assumptions of §3.2. → A probability space, measurable counts and epochs, independent Poisson increments, T>0, and AdmissibleRate on [0,T].; reason: These spell out the source model without continuity, boundedness or an assumed conditional law.
--   - generalization: The conditional law for n observed points (the text around (6) assumes n ≥ 1). → Every n ≥ 0, with the empty vector at n = 0, and the additional conclusions Λ(T) > 0, P(N(T) = n) > 0 and that the scaled one-arrival law is a probability measure.; reason: The n = 0 case is the trivial unit mass and the added conclusions follow from the §3.2 assumptions; at every n ≥ 1 the statement specializes to the source claim.
-- source:
--   Kim and Whitt, Are call center and hospital arrivals well modeled by nonhomogeneous Poisson processes?, Manufacturing Service Oper. Management 16(3), 2014, DOI 10.1287/msom.2014.0490, p. 471, THEOREM 1, PDF 8

import Mathlib
import Definitions.Def_NHPPArrivals_LinearRate_Supplement_ConditionalSample

namespace NHPPArrivals.LinearRate.Supplement

open MeasureTheory ProbabilityTheory

theorem conditioning {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (lam : ℝ → ℝ) (T c : ℝ) (hrate : AdmissibleRate lam T) (hc : 0 < c)
    (N : ℝ → Ω → ℕ) (X : ℕ → Ω → ℝ)
    (hN : IsNHPP P (fun s => c * lam s) T N X) :
    0 < cumRate lam T ∧
    IsProbabilityMeasure (scaledArrivalLaw lam T) ∧
    scaledArrivalLaw lam T = volume.withDensity (fun t => ENNReal.ofReal (condDensity lam T t)) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1,
      (scaledArrivalLaw lam T).real (Set.Iic t) = condCdf lam T t ∧
      condDensity lam T t = T * lam (t * T) / cumRate lam T) ∧
    (∀ n : ℕ, 0 < P {ω | N T ω = n} ∧
      conditionalVectorLaw P N X T n = orderedLaw (scaledArrivalLaw lam T) n) ∧
    scaledArrivalLaw (fun s => c * lam s) T = scaledArrivalLaw lam T ∧
    (∀ t ∈ Set.Icc (0 : ℝ) 1,
      condCdf (fun s => c * lam s) T t = condCdf lam T t) ∧
    (∀ t : ℝ, condDensity (fun s => c * lam s) T t = condDensity lam T t) := by sorry

end NHPPArrivals.LinearRate.Supplement
