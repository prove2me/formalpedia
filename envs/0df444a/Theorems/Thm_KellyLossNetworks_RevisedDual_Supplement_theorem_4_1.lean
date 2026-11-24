-- Prove2me | Theorems.Thm_KellyLossNetworks_RevisedDual_Supplement_theorem_4_1
-- name    : KellyLossNetworks.RevisedDual.Supplement.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T03:00:22.532877+00:00
-- url     : https://prove2.me/theorems/eb14f1b1-b665-479e-a388-5a74309c4c7b
-- title:
--   Theorem 4.1 — star functional limit and unique fluid flow
-- statement:
--   Fix the star model of §4 with capacity $C$, with fixed offered-load and route-selection parameters as the number of links $J$ grows. Here $C$ is a nonnegative integer, $w\ge1$ is the fixed number of links used per call, and $\lambda\ge0$ is the fixed offered rate involving each link. Let $X_{Jn}(t)$ be the fraction of links with $n$ busy circuits, and let the initial occupancy laws converge weakly to any probability law $\rho$ on $\Delta$.
--   $$X_J\Rightarrow X\quad\text{in }D_\Delta[0,\infty).$$
--   The limit is the unique flow, started with law $\rho$, satisfying (4.2):
--   $$\frac{d}{dt}\sum_{m=0}^n x_m(t)=(n+1)x_{n+1}(t)-b_n(x(t))x_n(t),\qquad n=0,\ldots,C-1,$$
--   where $b_n(x)=\lambda(1-x_C)^{w-1}$. The star has all $w$-subsets as routes and per-route rate $\lambda/\binom{J-1}{w-1}$, with $w\ge1$ fixed.
--
--   The result controls the full occupancy path law for arbitrary convergent initial distributions. The finite-network generator retains complete route counts, rather than treating links as independent birth–death chains.
--
--   Differences from the source:
--   - encoding: weak convergence in D_Δ[0,∞) → weak J1 convergence by bounded continuous tests, using the published càdlàg space; reason: the exact test-function characterization on the J1 Borel evaluation σ-algebra
--   - encoding: unique solution of the cumulative differential equations → existence of a measurable flow, its integral equations, and uniqueness for every initial vector in Δ; reason: the displayed drifts are continuous; integral and differentiable solution formulations are equivalent
--   - reading: networks with enough links to sample fixed route/trial sizes → rate-chain law required for all J beyond the finite sampling threshold; reason: only a finite initial segment is excluded from the asymptotic sequence; no initial law is restricted
--   - generalization: positive offered rates and circuit capacity → nonnegative offered rate and capacity, with w≥1 for the star and 0≤s≤C for reservation; reason: also includes zero arrivals and zero circuit capacity, where the equations still describe the process
-- source:
--   Kelly, Loss networks, Ann. Appl. Probab. 1(3):319–378 (1991), DOI 10.1214/aoap/1177005872, p. 344, Theorem 4.1

import Definitions.Def_KellyLossNetworks_RevisedDual_Supplement_NetworkChains

open scoped NNReal ENNReal

open MeasureTheory

namespace KellyLossNetworks.RevisedDual.Supplement

/-- Kelly (1991), Theorem 4.1, p. 344: full functional law of large
numbers and unique limiting flow for every convergent initial law.
**Formalization Note.** The finite process is the genuine route-count Markov chain, with
simultaneous release of all links held by each call. Path-law convergence uses the J1
bounded-continuous-test characterization. The ODE is in integral form; the limit has
continuous paths. Fixed route/trial parameters are independent of J. Small J outside the
network's sampling domain are irrelevant to the limit. -/
theorem theorem_4_1 (C w : ℕ) (lam : ℝ) (hw : 1 ≤ w) (hlam : 0 ≤ lam)
    (P : (J : ℕ) → Measure (RBMSensitivity.Cadlag (NetworkState J C (starRoutes J w))))
    (hP : ∀ J, max 1 w ≤ J → RandomRateChain (P J) (networkGenerator (starArrival J C w lam)))
    (rho : Measure (Fin (C+1) → ℝ)) [IsProbabilityMeasure rho]
    (hrho : rho (simplex C) = 1)
    (hinit : WeakInitial (fun J => (empiricalLaw (P J)).map (fun x => x 0)) rho) :
    ∃ F : (Fin (C+1) → ℝ) → (ℝ≥0 → (Fin (C+1) → ℝ)),
      Measurable F ∧
      (∀ z ∈ simplex C,
        FluidSolution (starBirth C w lam) z (F z) ∧
        ∀ x, FluidSolution (starBirth C w lam) z x → x = F z) ∧
      WeakJ1 (fun J => empiricalLaw (P J)) (rho.map F) := by sorry

end KellyLossNetworks.RevisedDual.Supplement
