-- Prove2me | Theorems.Thm_GJNSteadyState_Interchange_theorem_8
-- name    : GJNSteadyState.Interchange.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:51:38.07498+00:00
-- url     : https://prove2.me/theorems/32200758-1213-4f6f-8b54-a32098752850
-- title:
--   Theorem 8, p. 18 — the diffusion-scaled stationary distributions converge weakly to the RBM stationary distribution
-- statement:
--   Let $\Xi$ be a critically loaded generalized Jackson network ($\rho_j=1$ for all $j$) satisfying the standing assumptions of §2.1, let $\kappa^0>0$, and let $\Xi^n$ be the heavy-traffic sequence of §2.3, with $\rho^n_j=1-\kappa_j/\sqrt n$. Let $\pi^n$ be a stationary distribution of $\Xi^n$ (for all sufficiently large $n$) and let $\hat\pi^n$ be the law of $Q^n(0)/\sqrt n$ when $\bar Q^n(0)\sim\pi^n$, the stationary distribution of the rescaled queue length process $\hat Q^n(t)=Q^n(nt)/\sqrt n$. Then
--   $$\hat\pi^n\Rightarrow\pi_{\mathrm{RBM}}\qquad(n\to\infty),$$
--   where $\pi_{\mathrm{RBM}}$ is the unique stationary distribution of the reflected Brownian motion with parameters $(\beta,\Gamma,I-P')$ of Theorem 4.
--
--   The two limits $t\to\infty$ (steady state) and $n\to\infty$ (heavy traffic) can therefore be interchanged: the stationary distribution of the RBM is a valid approximation of the stationary queue lengths of the network in heavy traffic.
--
--   **Formalization Note** The conclusion asserts that the $(\beta,\Gamma,I-P')$-RBM has a stationary distribution $\nu$, that it has no other, and that the laws of $Q^n(0)/\sqrt n$ converge to $\nu$ in the topology of weak convergence of probability measures on $\mathbb R^J$. The sequence $\pi^n$ is arbitrary (stationary distributions need not be unique). The page writes "$(\beta,\Gamma,I-P)$-RBM"; the RBM of Theorem 4, $(\beta,\Gamma,I-P')$, is meant. The interarrival scaling of $\Xi^n$ is read as $a_j/(1-\kappa^0_j/\sqrt n)$ (see the definition of $\Xi^n$).
-- source:
--   Gamarnik and Zeevi, Validity of Heavy Traffic Steady-State Approximations in Generalized Jackson Networks, arXiv:math/0410066v2, p. 18, Theorem 8 (with π̂ⁿ defined in Section 4.2, p. 18, and πⁿ on p. 12)

import Mathlib
import Definitions.Def_Reiman84_QueueLength_Paths
import Definitions.Def_GJNSteadyState_Interchange_Network
import Definitions.Def_GJNSteadyState_Interchange_Dynamics
import Definitions.Def_GJNSteadyState_Interchange_HeavyTraffic
import Definitions.Def_GJNSteadyState_Interchange_RBM
open MeasureTheory Filter Topology Matrix

namespace GJNSteadyState.Interchange

/-- Theorem 8 (p. 18): for the heavy-traffic sequence `Ξⁿ` built from a critically loaded
GJN `Ξ` and `κ⁰ > 0`, and any sequence `πⁿ` of stationary distributions of `Ξⁿ`, the laws
`π̂ⁿ` of `Qⁿ(0)/√n` under `πⁿ` converge weakly to `π_RBM`, the unique stationary distribution of
the `(β, Γ, I − P′)`-RBM. -/
theorem theorem_8 {J : ℕ} (Ξ : Network J) (hΞ : Ξ.IsGJN) (hcrit : IsCritical Ξ)
    (κ0 : Fin J → ℝ) (hκ0 : ∀ j, 0 < κ0 j)
    (π : ℕ → Measure (State J)) [∀ n, IsProbabilityMeasure (π n)]
    (hπ : ∀ᶠ n in atTop, IsStationary (htNet Ξ κ0 n) (π n)) :
    ∃ ν : ProbabilityMeasure (Fin J → ℝ),
      IsRBMStationary Ξ.P (beta Ξ κ0) (Gamma Ξ) (ν : Measure (Fin J → ℝ)) ∧
      (∀ ν' : Measure (Fin J → ℝ), IsRBMStationary Ξ.P (beta Ξ κ0) (Gamma Ξ) ν' →
        ν' = (ν : Measure (Fin J → ℝ))) ∧
      Tendsto (fun n => scaledLaw (π n) n) atTop (𝓝 ν) := by sorry

end GJNSteadyState.Interchange
