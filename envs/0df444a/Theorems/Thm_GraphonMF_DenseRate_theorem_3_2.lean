-- Prove2me | Theorems.Thm_GraphonMF_DenseRate_theorem_3_2
-- name    : GraphonMF.DenseRate.theorem_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:28:15.424399+00:00
-- url     : https://prove2.me/theorems/635560bd-a8d3-44d6-b33f-cd660a991ddd
-- title:
--   Theorem 3.2, p. 3596 — maxᵢ E‖Xⁿ_i − X_{i/n}‖²_{*,T} ≤ κ/n for all n
-- statement:
--   Let $G:[0,1]^2\to[0,1]$ be a graphon and let $X=(X_u)_{u\in[0,1]}$ solve the graphon particle system
--   $$X_u(t)=X_u(0)+\int_0^t\!\!\int_I\!\int_{\mathbb R^d}b(X_u(s),x)G(u,v)\mu_{v,s}(dx)\,dv\,ds+\int_0^t\!\!\int_I\!\int_{\mathbb R^d}\sigma(X_u(s),x)G(u,v)\mu_{v,s}(dx)\,dv\,dB_u(s),\quad\mu_{u,t}=\mathcal L(X_u(t)),$$
--   driven by i.i.d. Brownian motions $B_u$ and independent initial states $X_u(0)\sim\mu_u(0)$. For each $n$ let $X^n=(X^n_1,\dots,X^n_n)$ solve the $n$-particle system
--   $$X^n_i(t)=X_{i/n}(0)+\int_0^t\frac1n\sum_{j=1}^n\xi^n_{ij}b(X^n_i(s),X^n_j(s))\,ds+\int_0^t\frac1n\sum_{j=1}^n\xi^n_{ij}\sigma(X^n_i(s),X^n_j(s))\,dB_{i/n}(s),$$
--   whose $i$-th particle uses the initial state and Brownian motion of the continuum particle at $u=i/n$.
--
--   Suppose:
--   1. (Condition 2.1) $u\mapsto\mu_u(0)$ is measurable, $\sup_u\mathbb E|X_u(0)|^{2+\varepsilon}<\infty$ for some $\varepsilon>0$, and $b$, $\sigma$ are Lipschitz;
--   2. (Condition 2.3) for finitely many intervals $I_1,\dots,I_N$ covering $[0,1]$, the initial laws are $W_2$-Lipschitz in $u$ on each $I_i$ and $G$ is Lipschitz on each block $I_i\times I_j$;
--   3. (Condition 3.2) the weights are sampled from $G$ itself: either $\xi^n_{ij}=G(i/n,j/n)$ for all $n$, or for all $n$, $\xi^n_{ij}=\xi^n_{ji}\sim\mathrm{Bernoulli}(G(i/n,j/n))$ independently for $1\le i\le j\le n$ and independently of $\{B_u,X_u(0)\}$.
--
--   Then there is a constant $\kappa\in(0,\infty)$ such that
--   $$\max_{i=1,\dots,n}\mathbb E\|X^n_i-X_{i/n}\|^2_{*,T}\le\frac{\kappa}{n}\qquad\text{for all }n\in\mathbb N.$$
--
--   The rate $1/n$ is the classical mean-field rate, and it is uniform over particles: every particle of the finite system is within $\kappa/n$ in mean square of the continuum particle with the same label, on the whole path.
--
--   **Formalization Note.** The constant $\kappa$ is chosen after the data ($b,\sigma,T,d,\varepsilon,\mu(0),G$, the noise and the weights) and before $n$ and $i$. The maximum over $i$ is stated as a bound for every $i$; at $n=0$ there is no particle. The statement quantifies over every solution of (2.1) and every solution of (3.1), which are unique by the Lipschitz property. $\mathbb E\|\cdot\|^2_{*,T}$ is a lower Lebesgue integral of the squared supremum over $[0,T]$, valued in $[0,\infty]$. The setting's conventions are listed in the Formalization Note of `GraphonMF.DenseRate.Setting`.
-- source:
--   Bayraktar, Chakraborty, Wu, Graphon mean field systems, Ann. Appl. Probab. 33(5) (2023), https://doi.org/10.1214/22-AAP1901, p. 3596, Condition 3.2 and Theorem 3.2, (3.5)

import Mathlib
import Definitions.Def_GraphonMF_DenseRate_Setting

open MeasureTheory ProbabilityTheory Filter Topology unitInterval
open scoped ENNReal NNReal

namespace GraphonMF.DenseRate

theorem theorem_3_2 {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (T : ℝ≥0) (hT : 0 < T)
    (P : Measure Ω) (μ0 : I → Measure (Fin d → ℝ)) (X0 : I → Ω → (Fin d → ℝ))
    (B : I → ℝ≥0 → Ω → Fin d → ℝ) (hN : NoiseSetting P μ0 X0 B)
    (ξ : (n : ℕ) → Ω → Fin n → Fin n → ℝ)
    (b : (Fin d → ℝ) → (Fin d → ℝ) → (Fin d → ℝ))
    (sigma : (Fin d → ℝ) → (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ)
    (ε : ℝ) (hε : 0 < ε) (h21 : Cond21 ε μ0 b sigma)
    (G : I → I → ℝ) (hG : IsGraphon G)
    {N : ℕ} (J : Fin N → Set I) (h23 : Cond23 μ0 G J)
    (h32 : Cond32 P X0 B ξ G)
    (X : I → ℝ≥0 → Ω → (Fin d → ℝ)) (hX : IsGraphonSolution T P X0 B G b sigma X) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (n : ℕ) (Xn : Fin n → ℝ≥0 → Ω → (Fin d → ℝ)),
      IsParticleSolution T P X0 B ξ b sigma n Xn →
      ∀ i : Fin n, ∫⁻ ω, supDistUpTo T (Xn i) (X (lab n i)) ω ^ 2 ∂P ≤
        ENNReal.ofReal (κ / (n : ℝ)) := by sorry

end GraphonMF.DenseRate
