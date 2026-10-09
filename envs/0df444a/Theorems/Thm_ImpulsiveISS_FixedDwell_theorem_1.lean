-- Prove2me | Theorems.Thm_ImpulsiveISS_FixedDwell_theorem_1
-- name    : ImpulsiveISS.FixedDwell.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T17:45:14.684865+00:00
-- url     : https://prove2.me/theorems/ab4fd218-9ff4-448d-966f-30d90e9f61e8
-- title:
--   Theorem 1 (corrected: max-form jump bound) — an ISS-Lyapunov function and the dwell-time condition (3.7) give ISS for every T ∈ S_θ
-- statement:
--   Let $X$ and $U$ be Banach spaces and consider the impulsive system
--   $$\dot x(t)=Ax(t)+f(x(t),u(t)),\quad t\notin T,\qquad x(t)=g(x^-(t),u^-(t)),\quad t\in T,$$
--   given through the transition map $\phi_c$ of its continuous part and its jump map $g$, with $x\equiv0$ an equilibrium. Let $V:X\to\mathbb R_+$ be continuous with
--   1. $\psi_1(\|x\|)\le V(x)\le\psi_2(\|x\|)$ for all $x$, where $\psi_1,\psi_2\in\mathcal K_\infty$ (3.1);
--   2. $V(x)\ge\gamma(\|\xi\|)\Rightarrow\dot V_u(x)\le-\varphi(V(x))$ for all $x\in X$, $\xi\in U$ and $u\in U_c$ with $u(0)=\xi$ (3.5);
--   3. $V(g(x,\xi))\le\max\{\alpha(V(x)),\gamma(\|\xi\|)\}$ for all $x\in X$, $\xi\in U$ (3.6);
--
--   where $\gamma\in\mathcal K_\infty$, $\alpha\in\mathcal P$ and $\varphi\in\mathcal P$. Suppose that for some $\theta,\delta>0$
--   $$\int_a^{\alpha(a)}\frac{ds}{\varphi(s)}\le\theta-\delta\qquad\text{for all }a>0. \tag{3.7}$$
--   Then the system is ISS for every impulse-time sequence $T=\{t_i\}$ with $t_{i+1}-t_i\ge\theta$ for all $i$ (the class $S_\theta$): there are $\beta\in\mathcal{KL}$ and $\gamma'\in\mathcal K_\infty$, possibly depending on $T$, with
--   $$\|x(t)\|\le\beta(\|x_0\|,t)+\gamma'(\|u\|_{U_c})\qquad\text{for all }x_0\in X,\ u\in U_c,\ t\ge0.$$
--
--   The condition (3.7) balances the growth that a jump may cause ($\alpha(a)>a$ is allowed) against the decay along the flow over a dwell time of length $\theta$. It is the fixed dwell-time counterpart of the paper's Theorem 5 and holds for Lyapunov functions that are not exponential.
--
--   **Formalization Note** Corrected statement: the jump hypothesis is the max form (3.6) of Proposition 3.1 for *all* $x,\xi$, in place of Definition 4's implication form ($V(x)\ge\chi(\|\xi\|)\Rightarrow V(g(x,\xi))\le\alpha(V(x))$), because the proof (p. 9, "$x(t_k)\in I_2$ by construction of the set $I_2$") bounds jumps from inside $\{V<\chi(\|\xi\|)\}$; as printed the theorem is false ($\dot x=-x$, $g(x,\xi)=x/2$ if $|\xi|\le|x|$ and $g(x,\xi)=1$ otherwise, $V=|x|$: from $x_0=0$ with $u\equiv\varepsilon$ the first jump reaches $1$ for every $\varepsilon>0$). The system is modelled by $(\phi_c,g)$ with the standing assumptions of the referenced setting; the initial time is $t_0=0$ (the paper's reduction (2.2)) and the first impulse is strictly after it. ISS uses a bound $M\ge\|u(t)\|$ in place of $\|u\|_{U_c}$. The integral in (3.7) is oriented (negative when $\alpha(a)<a$) and, for $a>0$, is a genuine Riemann integral because $\alpha(a)>0$ and $1/\varphi$ is continuous on $(0,\infty)$. $\beta$ is chosen after $T$ (non-uniform ISS, as in Remark 2).
-- source:
--   Dashkovskiy and Mironchenko, Input-to-state stability of nonlinear impulsive systems, arXiv:1212.5481v1, p. 6, Theorem 1 (with the jump bound (3.6) of Proposition 3.1, p. 5)

import Mathlib
import Definitions.Def_SmallGainISS_Lyapunov_Gains
import Definitions.Def_ProcessingNetworks_LyapunovCriteria_DiniDerivative
import Definitions.Def_ImpulsiveISS_FixedDwell_Setting

open scoped NNReal
open Filter Topology
open SmallGainISS.Lyapunov ProcessingNetworks.LyapunovCriteria

namespace ImpulsiveISS.FixedDwell

/-- **Theorem 1** (p. 6), corrected: the jump clause is the max form (3.6) of Proposition 3.1,
which is what the proof (p. 9) uses. Let `V` be an ISS-Lyapunov function in max form with
`ψ₁, ψ₂, γ ∈ 𝒦∞`, `α ∈ 𝒫`, and flow rate `φ ∈ 𝒫`. If for some `θ, δ > 0` and all `a > 0`
`∫_a^{α(a)} ds/φ(s) ≤ θ − δ` (3.7), then the system is ISS for every impulse-time sequence in
`S_θ` (with `β` allowed to depend on the sequence, Remark 2). -/
theorem theorem_1 {X U : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup U] [NormedSpace ℝ U] [CompleteSpace U]
    (S : System X U) (hS : IsImpulsiveSystem S)
    (V : X → ℝ≥0) (ψ₁ ψ₂ γ α φ : ℝ≥0 → ℝ≥0) (hV : IsISSLyapunovMax S V ψ₁ ψ₂ γ α φ)
    (hφ : IsPosDef φ) (θ δ : ℝ) (hθ : 0 < θ) (hδ : 0 < δ) (h37 : DwellCondition α φ θ δ)
    (τ : ℕ → ℝ) (hτ : InSTheta θ τ) :
    IsISS S τ := by sorry

end ImpulsiveISS.FixedDwell
