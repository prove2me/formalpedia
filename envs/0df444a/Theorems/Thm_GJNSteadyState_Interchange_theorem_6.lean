-- Prove2me | Theorems.Thm_GJNSteadyState_Interchange_theorem_6
-- name    : GJNSteadyState.Interchange.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:51:10.265216+00:00
-- url     : https://prove2.me/theorems/66bbb301-8402-49ae-bde8-18aa5f242559
-- title:
--   Theorem 6, p. 16 — exp(θΦ) is a geometric Lyapunov function and the stationary tail of Φ decays exponentially
-- statement:
--   Let $\kappa$ be the time-$t_0$ transition kernel of a Markov process on $\mathcal X$ with stationary distribution $\pi$, and let $\Phi$ be a measurable Lyapunov function with drift size $-\gamma<0$ and exception parameter $K$, with $\{\Phi>K\}\neq\emptyset$. Suppose $\theta>0$ satisfies
--   $$\theta\,L_2(\theta,t_0)\le\gamma. \tag{28}$$
--   Then:
--
--   1. $e^{\theta\Phi(\cdot)}$ is a geometric Lyapunov function with geometric drift size $1-\gamma\theta/2$, drift time $t_0$ and exception parameter $e^{\theta K}$;
--   2. for every $s>K$,
--   $$\mathbb P_\pi(\Phi(\Xi(0))>s)\le\Big(\frac{\gamma\theta}{2}\Big)^{-1}L_1(\theta,t_0)\,e^{-\theta(s-K)}. \tag{29}$$
--
--   Combined with Proposition 3 this gives the exponential tail bound of Theorem 7 on the scaled stationary workload.
--
--   **Formalization Note** The page prints the factor $(1-\gamma\theta/2)^{-1}$ in (29). Its proof (p. 24) applies (27) to $e^{\theta\Phi}$, whose geometric drift size is $1-\gamma\theta/2$ by the first part; (27) then gives $(1-(1-\gamma\theta/2))^{-1}=(\gamma\theta/2)^{-1}$ (the proof mislabels the drift size as $\gamma\theta/2$). The corrected factor is stated. The hypothesis $\{\Phi>K\}\neq\emptyset$ is added: Remark 6 derives $\gamma\theta\le1$, needed for the drift size $1-\gamma\theta/2$ to lie in $(0,1)$ as Definition 2 requires, by taking a supremum over this set. The Markov process enters through its time-$t_0$ transition kernel and the invariance of $\pi$. Condition (28) is read in $[0,\infty]$.
-- source:
--   Gamarnik and Zeevi, Validity of Heavy Traffic Steady-State Approximations in Generalized Jackson Networks, arXiv:math/0410066v2, p. 16, Theorem 6, (28)–(29), Remark 6; proof p. 24

import Mathlib
import Definitions.Def_GJNSteadyState_Interchange_Lyapunov
open MeasureTheory ProbabilityTheory

namespace GJNSteadyState.Interchange

/-- Theorem 6 (p. 16): let `π` be a stationary distribution of a Markov process with time-`t₀`
transition kernel `κ`, and `Φ` a Lyapunov function with parameters `γ, t₀, K` such that
`{Φ > K}` is nonempty. If `θ > 0` satisfies (28) `θ L₂(θ, t₀) ≤ γ`, then `exp(θΦ)` is a
geometric Lyapunov function with geometric drift size `1 − γθ/2`, drift time `t₀` and exception
parameter `e^{θK}`, and (29) `P_π(Φ(Ξ(0)) > s) ≤ (γθ/2)⁻¹ L₁(θ, t₀) e^{−θ(s − K)}` for every
`s > K`. The page prints the factor `(1 − γθ/2)⁻¹` in (29); applying (27) to the geometric drift
size `1 − γθ/2` of the first part gives `(1 − (1 − γθ/2))⁻¹ = (γθ/2)⁻¹`, which is stated here. -/
theorem theorem_6 {X : Type*} [MeasurableSpace X] (κ : Kernel X X) [IsMarkovKernel κ]
    (π : Measure X) [IsProbabilityMeasure π] (hπ : κ.Invariant π)
    (Φ : X → NNReal) (hΦ : Measurable Φ) (γ K : ℝ)
    (hlyap : IsLyapunov (kernelExp κ) Φ γ K) (hne : ∃ x, K < (Φ x : ℝ))
    (θ : ℝ) (hθ : 0 < θ) (h28 : ENNReal.ofReal θ * L2 (kernelExp κ) Φ θ ≤ ENNReal.ofReal γ) :
    IsGeomLyapunov (kernelExp κ) (fun x => Real.toNNReal (Real.exp (θ * Φ x)))
        (1 - γ * θ / 2) (Real.exp (θ * K)) ∧
      ∀ s : ℝ, K < s →
        π {x | s < (Φ x : ℝ)} ≤
          (ENNReal.ofReal (γ * θ / 2))⁻¹ * L1 (kernelExp κ) Φ θ *
            ENNReal.ofReal (Real.exp (-(θ * (s - K)))) := by sorry

end GJNSteadyState.Interchange
