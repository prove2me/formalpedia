-- Prove2me | Theorems.Thm_KellyStochasticNetworks_LossLimits_product_law_normalized
-- name    : KellyStochasticNetworks.LossLimits.product_law_normalized
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-22T03:47:53.616322+00:00
-- url     : https://prove2.me/theorems/837c7ecc-94fc-401c-a049-809050c32fb3
-- title:
--   Equation (3.3) — normalized loss-network product law
-- statement:
--   Fix finite sets of links and routes, a natural circuit-requirement matrix $A$, natural capacities $C$, and strictly positive rates $\nu_r$. Let $S(C)=\{n\in\mathbb N^R:An\le C\}$ and $w_\nu(n)=\prod_r\nu_r^{n_r}/n_r!$. The actual partition sum $Z=\sum_{n\in S(C)}w_\nu(n)$ is strictly positive and the sum converges to $Z$. Its normalized masses satisfy detailed balance for the loss-network rates: admitted route-$r$ arrivals have rate $\nu_r$ and departures have rate $n_r$. The constructed occupancy measure is a probability measure, supported on $S(C)$, with
--   $$\pi\{n\}=Z^{-1}\prod_r\frac{\nu_r^{n_r}}{n_r!}\quad(n\in S(C)).$$
--
--   This supplies the actual normalizer required by the published product-form detailed-balance theorem, instead of assuming the normalizing sum exists. It identifies the distribution used in the Gaussian limit.
--
--   **Formalization Note** The book's $G(C)$ is $Z^{-1}$. The state space is countable; zero columns of $A$ are allowed and can make $S(C)$ infinite. No probability normalization or summability is assumed.
-- source:
--   Kelly & Yudovina, Stochastic Networks (2014), supplied Lecture Notes PDF, printed p. 53 (PDF p. 61), Eq. (3.3); DOI 10.1017/cbo9781139565363.

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyStochasticNetworks_LossLimits_Laws

open MeasureTheory

namespace KellyStochasticNetworks.LossLimits

/-- The actual normalizer in (3.3), discharging the summability hypothesis
of the published detailed-balance theorem. `partition` is the sum of the
published weights over the published feasible-state subtype, and `occupancyLaw`
is the sum of Dirac masses weighted by weight / partition. -/
theorem product_law_normalized {J R : ℕ} (A : Fin J → Fin R → ℕ)
    (ν : Fin R → ℝ) (C : Fin J → ℕ) (hν : ∀ r, 0 < ν r) :
    0 < partition A ν C ∧
    HasSum (fun n : KellyStochasticNetworks.lossStates A C =>
      KellyStochasticNetworks.lossWeight ν (n : Fin R → ℕ)) (partition A ν C) ∧
    KellyStochasticNetworks.DetailedBalance
      (fun n : KellyStochasticNetworks.lossStates A C =>
        KellyStochasticNetworks.lossWeight ν (n : Fin R → ℕ) / partition A ν C)
      (KellyStochasticNetworks.truncatedRates
        (KellyStochasticNetworks.openMigrationRates (fun _ _ => (0 : ℝ))
          (fun _ => 1) ν (fun _ m => (m : ℝ)))
        (KellyStochasticNetworks.lossStates A C)) ∧
    IsProbabilityMeasure (occupancyLaw A ν C) ∧
    (∀ n : KellyStochasticNetworks.lossStates A C,
      (occupancyLaw A ν C) {(n : Fin R → ℕ)} =
        ENNReal.ofReal (KellyStochasticNetworks.lossWeight ν (n : Fin R → ℕ) / partition A ν C)) ∧
    (occupancyLaw A ν C) (KellyStochasticNetworks.lossStates A C)ᶜ = 0 := by sorry

end KellyStochasticNetworks.LossLimits
