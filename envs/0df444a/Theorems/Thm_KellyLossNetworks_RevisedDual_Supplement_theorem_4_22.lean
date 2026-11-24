-- Prove2me | Theorems.Thm_KellyLossNetworks_RevisedDual_Supplement_theorem_4_22
-- name    : KellyLossNetworks.RevisedDual.Supplement.theorem_4_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T03:01:10.268684+00:00
-- url     : https://prove2.me/theorems/7545e9b9-490c-4e64-bbe4-95a883e4d32a
-- title:
--   Theorem 4.22 — exchangeable alternative-routing functional limit and unique fluid flow
-- statement:
--   Fix the exchangeable alternative-routing model of §4 with capacity $C$, with fixed offered-load and route-selection parameters as the number of links $J$ grows. Here $C$ is a nonnegative integer and $\nu\ge0$ is the fixed Poisson offered rate at each first-choice link. Let $X_{Jn}(t)$ be the fraction of links with $n$ busy circuits, and let the initial occupancy laws converge weakly to any probability law $\rho$ on $\Delta$.
--   $$X_J\Rightarrow X\quad\text{in }D_\Delta[0,\infty).$$
--   The limit is the unique flow, started with law $\rho$, satisfying (4.23):
--   $$\frac{d}{dt}\sum_{m=0}^n x_m(t)=(n+1)x_{n+1}(t)-b_n(x(t))x_n(t),\qquad n=0,\ldots,C-1,$$
--   where $b_n(x)=\nu+2\nu x_C(1-x_C)$. Every blocked first-choice arrival tries one uniformly chosen pair of other links; both circuits are held and released together.
--
--   The result controls the full occupancy path law for arbitrary convergent initial distributions. The finite-network generator retains complete route counts, rather than treating links as independent birth–death chains.
--
--   Differences from the source:
--   - encoding: weak convergence in D_Δ[0,∞) → weak J1 convergence by bounded continuous tests, using the published càdlàg space; reason: the exact test-function characterization on the J1 Borel evaluation σ-algebra
--   - encoding: unique solution of the cumulative differential equations → existence of a measurable flow, its integral equations, and uniqueness for every initial vector in Δ; reason: the displayed drifts are continuous; integral and differentiable solution formulations are equivalent
--   - reading: networks with enough links to sample fixed route/trial sizes → rate-chain law required for all J beyond the finite sampling threshold; reason: only a finite initial segment is excluded from the asymptotic sequence; no initial law is restricted
--   - generalization: positive offered rates and circuit capacity → nonnegative offered rate and capacity, with w≥1 for the star and 0≤s≤C for reservation; reason: also includes zero arrivals and zero circuit capacity, where the equations still describe the process
--   - generalization: J=K(K−1)/2 links in the motivating complete graph → every sufficiently large integer number J of exchangeable links; reason: the simplified model and its transition rule depend only on the links, so this includes the source triangular subsequence
-- source:
--   Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872, p. 350, Theorem 4.22

import Definitions.Def_KellyLossNetworks_RevisedDual_Supplement_NetworkChains

open scoped NNReal ENNReal

open MeasureTheory

namespace KellyLossNetworks.RevisedDual.Supplement

/-- Kelly (1991), Theorem 4.22, p. 350: full functional law of large
numbers and unique limiting flow for every convergent initial law.
**Formalization Note.** The finite process is the genuine route-count Markov chain, with
simultaneous release of all links held by each call. Path-law convergence uses the J1
bounded-continuous-test characterization. The ODE is in integral form; the limit has
continuous paths. Fixed route/trial parameters are independent of J. Small J outside the
network's sampling domain are irrelevant to the limit. -/
theorem theorem_4_22 (C : ℕ) (nu : ℝ) (hnu : 0 ≤ nu)
    (P : (J : ℕ) → Measure (RBMSensitivity.Cadlag (NetworkState J C (alternativeRoutes J))))
    (hP : ∀ J, 3 ≤ J → RandomRateChain (P J) (networkGenerator (alternativeArrival J C 0 1 nu)))
    (rho : Measure (Fin (C+1) → ℝ)) [IsProbabilityMeasure rho]
    (hrho : rho (simplex C) = 1)
    (hinit : WeakInitial (fun J => (empiricalLaw (P J)).map (fun x => x 0)) rho) :
    ∃ F : (Fin (C+1) → ℝ) → (ℝ≥0 → (Fin (C+1) → ℝ)),
      Measurable F ∧
      (∀ z ∈ simplex C,
        FluidSolution (trunkBirth C 0 1 nu) z (F z) ∧
        ∀ x, FluidSolution (trunkBirth C 0 1 nu) z x → x = F z) ∧
      WeakJ1 (fun J => empiricalLaw (P J)) (rho.map F) := by sorry

end KellyLossNetworks.RevisedDual.Supplement
