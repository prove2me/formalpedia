-- Prove2me | Theorems.Thm_GJNSteadyState_Interchange_theorem_5
-- name    : GJNSteadyState.Interchange.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:49:54.657986+00:00
-- url     : https://prove2.me/theorems/61d28746-dc0c-4e39-ad5d-852c76562eef
-- title:
--   Theorem 5, p. 15 — a geometric Lyapunov function bounds E_π Φ by φ(t₀)K/(1 − γ)
-- statement:
--   Let $\kappa$ be the time-$t_0$ transition kernel of a Markov process on $\mathcal X$ and let $\pi$ be a stationary distribution, so that $\pi\kappa=\pi$. Let $\Phi:\mathcal X\to\mathbb R_+$ be measurable and a geometric Lyapunov function with geometric drift size $0<\gamma<1$ and exception parameter $K$, and suppose $\phi(t_0)=\sup_x\Phi(x)^{-1}\mathbb E_x\Phi(\Xi(t_0))$ is finite. Then
--   $$\mathbb E_\pi[\Phi(\Xi(0))]\le\frac{\phi(t_0)\,K}{1-\gamma}. \tag{27}$$
--   The bound holds for every stationary distribution, unique or not.
--
--   It is the basic tool of the paper: applied to $e^{\theta\Phi}$ it yields the exponential tail bound of Theorem 6.
--
--   **Formalization Note** The Markov process enters only through its time-$t_0$ transition kernel and the invariance $\pi\kappa=\pi$ of a stationary law, which is all the statement uses. The hypothesis $\phi(t_0)<\infty$ is the page's remark "the bound is only meaningful when $\phi(t_0)$ is finite"; it is needed in $[0,\infty]$ arithmetic, where $\infty\cdot0=0$ would otherwise turn $K=0$ into a false claim. $K$ enters as $\max(K,0)$; for $K<0$ the geometric drift holds everywhere and both sides are $0$. The expectation is a lower Lebesgue integral and may a priori be infinite.
-- source:
--   Gamarnik and Zeevi, Validity of Heavy Traffic Steady-State Approximations in Generalized Jackson Networks, arXiv:math/0410066v2, p. 15, Theorem 5, (27)

import Mathlib
import Definitions.Def_GJNSteadyState_Interchange_Lyapunov
open MeasureTheory ProbabilityTheory

namespace GJNSteadyState.Interchange

/-- Theorem 5 (p. 15): if `π` is a stationary distribution of a Markov process whose time-`t₀`
transition kernel is `κ`, and `Φ` is a geometric Lyapunov function with parameters `γ, t₀, K`,
then `E_π Φ(Ξ(0)) ≤ φ(t₀) K / (1 − γ)`. -/
theorem theorem_5 {X : Type*} [MeasurableSpace X] (κ : Kernel X X) [IsMarkovKernel κ]
    (π : Measure X) [IsProbabilityMeasure π] (hπ : κ.Invariant π)
    (Φ : X → NNReal) (hΦ : Measurable Φ) (γ K : ℝ)
    (hgeo : IsGeomLyapunov (kernelExp κ) Φ γ K)
    (hphi : phiSup (kernelExp κ) Φ < ⊤) :
    ∫⁻ x, (Φ x : ENNReal) ∂π ≤
      phiSup (kernelExp κ) Φ * ENNReal.ofReal K / ENNReal.ofReal (1 - γ) := by sorry

end GJNSteadyState.Interchange
