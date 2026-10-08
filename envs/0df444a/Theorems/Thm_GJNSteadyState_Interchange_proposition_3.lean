-- Prove2me | Theorems.Thm_GJNSteadyState_Interchange_proposition_3
-- name    : GJNSteadyState.Interchange.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:51:34.52888+00:00
-- url     : https://prove2.me/theorems/8af6722b-5a34-4ec3-b150-f184305d9694
-- title:
--   Proposition 3, p. 17 — Φ = w′z is a Lyapunov function for Ξⁿ with drift −√n, drift time nt₀, exception c₀√n
-- statement:
--   Let $\Xi^n$ be the heavy-traffic sequence built from a critically loaded GJN $\Xi$ and $\kappa^0>0$. There are constants $t_0,c_0,\theta_0>0$, depending only on $\Xi$, such that for all sufficiently large $n$ the function $\Phi(z,a,v)=w'z$ is a Lyapunov function for the Markov process $\bar Q^n$ with drift size parameter $-\sqrt n$, drift time parameter $nt_0$ and exception parameter $c_0\sqrt n$; in addition
--   $$\limsup_{n\to\infty}L_1(\theta_0/\sqrt n,\,nt_0)<\infty, \tag{33}$$
--   $$\limsup_{n\to\infty}\frac1nL_2(\theta_0/\sqrt n,\,nt_0)<\infty, \tag{34}$$
--   where $L_1,L_2$ are computed for $\bar Q^n$ and $\Phi$.
--
--   Together with Theorem 6 this yields the uniform exponential tail bound of Theorem 7.
--
--   **Formalization Note** The constants are those of Proposition 2 on the page; as a separate statement they are existentially quantified here, before $n$. $L_1,L_2$ and the Lyapunov condition use the expectation operator of $\bar Q^n$ at time $nt_0$ on its state space $\mathcal X$ (`expectOn`; the suprema in $L_1$, $L_2$ and the Lyapunov condition range over $\mathcal X$, as on the page), and both limsups are rendered as one finite bound valid for all large $n$.
-- source:
--   Gamarnik and Zeevi, Validity of Heavy Traffic Steady-State Approximations in Generalized Jackson Networks, arXiv:math/0410066v2, p. 17, Proposition 3, (33)–(34)

import Mathlib
import Definitions.Def_GJNSteadyState_Interchange_Network
import Definitions.Def_GJNSteadyState_Interchange_Dynamics
import Definitions.Def_GJNSteadyState_Interchange_HeavyTraffic
import Definitions.Def_GJNSteadyState_Interchange_Lyapunov
open MeasureTheory Filter Topology Matrix

namespace GJNSteadyState.Interchange

/-- Proposition 3 (p. 17): there are `t₀, c₀, θ₀ > 0` depending only on `Ξ` such that, for all
large `n`, the workload `Φ(z, a, v) = w′z` is a Lyapunov function for `Q̄ⁿ` on its state space
`𝒳 = ℤ₊^J × ℝ₊^{2J}` with drift size
parameter `−√n`, drift time `nt₀` and exception parameter `c₀√n`; and (33)
`limsup_n L₁(θ₀/√n, nt₀) < ∞`, (34) `limsup_n n⁻¹ L₂(θ₀/√n, nt₀) < ∞`. -/
theorem proposition_3 {J : ℕ} (Ξ : Network J) (hΞ : Ξ.IsGJN) (hcrit : IsCritical Ξ)
    (κ0 : Fin J → ℝ) (hκ0 : ∀ j, 0 < κ0 j) :
    ∃ t₀ c₀ θ₀ : ℝ, 0 < t₀ ∧ 0 < c₀ ∧ 0 < θ₀ ∧
      (∀ᶠ n : ℕ in atTop,
        IsLyapunov (fun x f => expectOn (htNet Ξ κ0 n) x (n * t₀) f) (fun x => workload Ξ x.1)
          (Real.sqrt n) (c₀ * Real.sqrt n)) ∧
      ∃ C : NNReal, ∀ᶠ n : ℕ in atTop,
        L1 (fun x f => expectOn (htNet Ξ κ0 n) x (n * t₀) f) (fun x => workload Ξ x.1)
            (θ₀ / Real.sqrt n) ≤ C ∧
          ENNReal.ofReal (1 / (n : ℝ)) *
              L2 (fun x f => expectOn (htNet Ξ κ0 n) x (n * t₀) f) (fun x => workload Ξ x.1)
                (θ₀ / Real.sqrt n) ≤ C := by sorry

end GJNSteadyState.Interchange
