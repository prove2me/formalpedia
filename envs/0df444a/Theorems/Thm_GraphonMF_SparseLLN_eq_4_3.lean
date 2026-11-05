-- Prove2me | Theorems.Thm_GraphonMF_SparseLLN_eq_4_3
-- name    : GraphonMF.SparseLLN.eq_4_3
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-04T22:32:45.288178+00:00
-- url     : https://prove2.me/theorems/711ab8ce-eccf-4aa6-9cb8-db1632b63f73
-- title:
--   Theorem 4.1, (4.3) — empirical-law LLN for the percolated particle system
-- statement:
--   Consider the percolated $n$-particle system (4.1),
--   $$X_i^n(t)=X_{i/n}(0)+\int_0^t\frac1{n\beta_n}\sum_{j=1}^n\xi_{ij}^n\,b(X_i^n(s),X_j^n(s))\,ds+\int_0^t\sigma(X_i^n(s))\,dB_{i/n}(s),\qquad i=1,\dots,n,$$
--   and the limiting graphon particle system (4.2),
--   $$X_u(t)=X_u(0)+\int_0^t\!\int_I\!\int_{\mathbb R^d} b(X_u(s),x)\,G(u,v)\,\mu_{v,s}(dx)\,dv\,ds+\int_0^t\sigma(X_u(s))\,dB_u(s),\qquad \mu_{u,t}=\mathcal L(X_u(t)),$$
--   driven by the same independent initial states and Brownian motions $\{X_u(0),B_u: u\in I\}$.
--
--   Assume Condition 2.2(a) (finitely many intervals covering $I$ on each of which $u\mapsto\mathcal L(X_u(0))$ is $W_2$-continuous), Condition 4.1 (measurable initial laws with uniformly bounded second moments; $b$ bounded and Lipschitz; $\sigma$ bounded, Lipschitz, invertible with bounded inverse; $\beta_n\in(0,1]$ and $n\beta_n\to\infty$) and Condition 4.2 ($G_n$ is a step graphon on the grid of mesh $1/n$; $\xi^n_{ij}=\xi^n_{ji}$ are independent $\mathrm{Bernoulli}(\beta_nG_n(i/n,j/n))$ for $i\le j$, independent of the noise; and $\|G_n-G\|_\square\to0$). Let
--   $$\mu^n:=\frac1n\sum_{i=1}^n\delta_{X_i^n},\qquad \bar\mu:=\int_I\mathcal L(X_u)\,du .$$
--   Then
--   $$\mu^n\longrightarrow\bar\mu\quad\text{in }\mathcal P(\mathcal C_d)\text{ in probability as }n\to\infty. \tag{4.3}$$
--
--   **Formalization notes.** This is the first clause of Theorem 4.1, stated with exactly the same hypotheses and objects as the mission goal `GraphonMF.SparseLLN.theorem_4_1` (Condition 2.2(b) is not assumed). Empirical measures are indexed by $n+1$ so that they are defined; convergence in probability is in the weak topology of $\mathcal P(\mathcal C_d)$: for every neighbourhood $U$ of $\bar\mu$, $\mathbb P(\mu^{n}\notin U)\to0$ (outer measure). In the paper this is proved (Section 7.2) by approximating $G$ in operator norm by a continuous graphon $\tilde G$ (Lusin), using the stability estimate of Theorem 2.1(c), Lemma 6.2 for $\tilde G$, and Lemma 7.2 with Remark 2.1.
-- source:
--   Bayraktar, Chakraborty, Wu, Graphon mean field systems, Ann. Appl. Probab. 33(5) (2023), pp. 3597–3598, Theorem 4.1, display (4.3); proof in Section 7.2, p. 3615; https://doi.org/10.1214/22-AAP1901 (arXiv:2003.13180)

import Definitions.Def_GraphonMF_SparseLLN_Setting

open MeasureTheory Filter Topology
open scoped ENNReal NNReal
set_option autoImplicit false

namespace GraphonMF.SparseLLN

/-- Theorem 4.1, display (4.3), pp. 3597–3598: under Conditions 2.2(a), 4.1 and 4.2 the
empirical law of the percolated particle system converges in probability to `∫_I Law(X_u) du`. -/
theorem eq_4_3
    {T : ℝ≥0} {d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    (hT : 0 < T) (hd : 0 < d)
    (P : Measure Ω) (X0 : GraphonMF.Stability.I → Ω → Vec d) (B : GraphonMF.Stability.I → ℝ≥0 → Ω → Vec d)
    (hnoise : NoiseSetting P X0 B)
    (G : GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ) (hG : GraphonMF.Stability.IsGraphon G)
    (b : Vec d → Vec d → Vec d) (σ : Vec d → Matrix (Fin d) (Fin d) ℝ)
    (β : ℕ → ℝ) (h41 : Cond41 (initialLaw P X0) b σ β)
    (N : ℕ) (J : Fin N → Set GraphonMF.Stability.I)
    (h22a : Cond22a (initialLaw P X0) J)
    (Gs : ℕ → GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ)
    (ξ : (n : ℕ) → Ω → Fin n → Fin n → ℝ)
    (hξ : ∀ n i j, Measurable (fun ω => ξ n ω i j))
    (h42 : Cond42 P X0 B ξ Gs β G)
    (X : GraphonMF.Stability.I → Ω → GraphonMF.Stability.Cd T d)
    (hX : IsGraphonSolution42 P X0 B hnoise G b σ X)
    (Xn : (n : ℕ) → Fin n → Ω → GraphonMF.Stability.Cd T d)
    (hXn : ∀ n, IsParticleSolution41 P X0 B hnoise ξ hξ β b σ n (Xn n)) :
    ConvergesInProbability P (empiricalSeq Xn) (solutionMixture hX) := by sorry

end GraphonMF.SparseLLN
