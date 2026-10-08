-- Prove2me | Theorems.Thm_GJNSteadyState_Interchange_theorem_4
-- name    : GJNSteadyState.Interchange.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:51:33.681239+00:00
-- url     : https://prove2.me/theorems/a63daf78-db43-46d1-8693-be92806fa432
-- title:
--   Theorem 4, p. 14 — Qⁿ(n·)/√n converges weakly to the (β, Γ, I − P′)-RBM uniformly on [0, T]
-- statement:
--   Let $\Xi^n$ be the heavy-traffic sequence built from a critically loaded GJN $\Xi$ and $\kappa^0>0$, so that $\rho^n$ satisfies (17). Suppose the networks are started from initial laws $\mu^n_0$ on $\mathcal X$ such that $Q^n(0)/\sqrt n\Rightarrow Z(0)$, where $Z(0)$ has law $\pi_0$ on $\mathbb R^J_+$. Then for every $T>0$ the processes
--   $$\big(Q^n(nt')/\sqrt n:\ 0\le t'\le T\big)$$
--   converge weakly, with respect to the topology of uniform convergence in $\mathcal D[0,T]$, to the RBM $(Z(t'):0\le t'\le T)$ with initial distribution $Z(0)\sim\pi_0$ and parameters $(\beta,\Gamma,I-P')$, where $\beta=-(I-P')M^{-1}\kappa$ and
--   $$\Gamma_{k\ell}=\sum_{j=1}^J\mu_j\big[p_{jk}(\delta_{k\ell}-p_{j\ell})+c^2_{s,j}(p_{jk}-\delta_{jk})(p_{j\ell}-\delta_{j\ell})\big]+\alpha_kc^2_{a,k}\delta_{k\ell}.$$
--
--   This is Reiman's heavy-traffic limit theorem, extended to a general initial condition; it identifies every weak limit point of the stationary laws in Theorem 8.
--
--   **Formalization Note** The limit RBM is any process $Z$ with $Z(0)\sim\pi_0$ independent of a Brownian motion $\xi$ with drift $\beta$ and covariance $\Gamma$, solving the Skorohod problem for $Z(0)+\xi$ almost surely; the statement holds for every such $Z$. The initial laws $\mu^n_0$ are laws on $\mathcal X$ (`InStateSpace`: nonnegative elapsed times); their elapsed-time coordinates are otherwise unrestricted, as on the page. Weak convergence is in coupling form (`WeakConvUnif`). A realization of $\Xi^n$ is given for every $n$; for small $n$ the network $\Xi^n$ is degenerate but still has realizations, and only large $n$ enter the conclusion. The published `Reiman84.QueueLength.queue_length_heavy_traffic_limit` (Open) is the special case $Q^n(0)=0$ under Reiman's own parametrisation, in the $J_1$ topology on $[0,1]$; it is not the same statement.
-- source:
--   Gamarnik and Zeevi, Validity of Heavy Traffic Steady-State Approximations in Generalized Jackson Networks, arXiv:math/0410066v2, p. 14, Theorem 4 (cited: Reiman 1984, extended to general initial laws as in Chen–Yao, Ch. 7)

import Mathlib
import Definitions.Def_Reiman84_QueueLength_Paths
import Definitions.Def_GJNSteadyState_Interchange_Network
import Definitions.Def_GJNSteadyState_Interchange_Dynamics
import Definitions.Def_GJNSteadyState_Interchange_HeavyTraffic
import Definitions.Def_GJNSteadyState_Interchange_RBM
open MeasureTheory Filter Topology Matrix ProbabilityTheory

namespace GJNSteadyState.Interchange

/-- Theorem 4 (p. 14, Reiman): for the heavy-traffic sequence `Ξⁿ` (with `ρⁿ` as in (17)),
if the initial laws (laws on the state space `𝒳 = ℤ₊^J × ℝ₊^{2J}`) satisfy
`Qⁿ(0)/√n ⇒ Z(0) ∼ π₀`, a probability measure on `ℝ₊^J`, then for
every `T > 0` the processes `(Qⁿ(nt′)/√n : 0 ≤ t′ ≤ T)` converge weakly, in `𝒟[0, T]` with the
uniform topology, to the RBM `(Z(t′) : 0 ≤ t′ ≤ T)` with `Z(0) ∼ π₀` and parameters
`(β, Γ, I − P′)`, `β = −(I − P′)M⁻¹κ` and `Γ` as displayed on p. 14. -/
theorem theorem_4 {J : ℕ} (Ξ : Network J) (hΞ : Ξ.IsGJN) (hcrit : IsCritical Ξ)
    (κ0 : Fin J → ℝ) (hκ0 : ∀ j, 0 < κ0 j)
    (μ0 : ℕ → Measure (State J)) [∀ n, IsProbabilityMeasure (μ0 n)]
    (hμ0 : ∀ n, μ0 n {x | ¬ InStateSpace x} = 0)
    (π0 : ProbabilityMeasure (Fin J → ℝ))
    (hπ0 : (π0 : Measure (Fin J → ℝ)) {z | ¬ (0 ≤ z)} = 0)
    (hconv : Tendsto (fun n => scaledLaw (μ0 n) n) atTop (𝓝 π0))
    (R : ∀ n : ℕ, Realization (htNet Ξ κ0 n) (μ0 n))
    (T : ℝ) (hT : 0 < T)
    (Ω' : Type) [MeasurableSpace Ω'] (Pr : Measure Ω') (Z0 : Ω' → Fin J → ℝ)
    (ξ : Ω' → ℝ → Fin J → ℝ) (Y Z : Ω' → ℝ → Fin J → ℝ)
    (hZ0 : Measurable Z0) (hZ0law : Pr.map Z0 = (π0 : Measure (Fin J → ℝ)))
    (hξ : Reiman84.QueueLength.IsDriftedBM (beta Ξ κ0) (Gamma Ξ) Pr ξ)
    (hind : IndepFun Z0 ξ Pr)
    (hrefl : ∀ᵐ ω ∂Pr,
      Reiman84.QueueLength.IsReflectionPair Ξ.P (fun t => Z0 ω + ξ ω t) (Y ω) (Z ω)) :
    WeakConvUnif T (fun n => (R n).P)
      (fun n ω t => fun j => ((R n).Q (n * t) ω j : ℝ) / Real.sqrt n) Pr Z := by sorry

end GJNSteadyState.Interchange
