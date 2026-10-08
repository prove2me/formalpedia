-- Prove2me | Theorems.Thm_GraphonMF_DenseLLN_theorem_3_1
-- name    : GraphonMF.DenseLLN.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:30:27.552636+00:00
-- url     : https://prove2.me/theorems/dd1b0c9d-179f-4666-9255-bdb47f967e71
-- title:
--   Theorem 3.1, p. 3595 — μⁿ → μ̄ in 𝒫(𝒞_d) in probability; under 2.2(b) also (1/n) Σᵢ E‖Xⁿ_i − X_{i/n}‖²_{*,T} → 0
-- statement:
--   Let $I=[0,1]$, $T>0$, and let the initial states $X_u(0)\sim\mu_u(0)$ and Brownian motions $B_u$, $u\in I$, be mutually independent on one probability space. Assume:
--
--   1. Condition 2.1: $u\mapsto\mu_u(0)$ is measurable, $\sup_u\mathbb E|X_u(0)|^{2+\varepsilon}<\infty$ for some $\varepsilon>0$, and $b,\sigma$ are Lipschitz;
--   2. Condition 2.2(a): for a finite cover of $I$ by intervals $I_1,\dots,I_N$, $u\mapsto\mu_u(0)$ is $W_2$-continuous on each $I_i$;
--   3. Condition 3.1: $G_n$ are step graphons (3.2); the weights satisfy either $\xi^n_{ij}=G_n(i/n,j/n)$, or $\xi^n_{ij}=\xi^n_{ji}\sim\mathrm{Bernoulli}(G_n(i/n,j/n))$ independently for $i\le j$ and independently of the noise; and $G_n\to G$ in the cut metric for a graphon $G$.
--
--   Let $X=(X_u)$ solve the graphon particle system (2.1) for $G$, with path laws $\mu_u$, and let $X^n$ solve the $n$-particle system (3.1), driven by $X_{i/n}(0)$ and $B_{i/n}$. Then
--   $$\mu^n:=\frac1n\sum_{i=1}^n\delta_{X^n_i}\ \longrightarrow\ \bar\mu:=\int_I\mu_u\,du\quad\text{in }\mathcal P(\mathcal C_d)\text{ in probability}\tag{3.3}$$
--   as $n\to\infty$. If in addition Condition 2.2(b) holds for the same intervals (for each interior point $u$ of $I_i$, $G$ is continuous at $(u,v)$ for a.e. $v$), then
--   $$\frac1n\sum_{i=1}^n\mathbb E\big\|X^n_i-X_{i/n}\big\|_{*,T}^2\longrightarrow0 .\tag{3.4}$$
--
--   This is the law of large numbers for diffusions interacting through a dense weighted graph whose weights converge to a graphon in the cut metric. The regularity Condition 2.2(b) is needed only for the $L^2$ statement (3.4).
--
--   **Formalization Note** Convergence in probability means: for every neighbourhood $U$ of $\bar\mu$ in the weak topology, $\mathbb P(\mu^n\notin U)\to0$, with $\mathbb P$ applied as an outer measure. $\bar\mu$ is the mixture $\int_I\mu_u\,du$, a probability measure because the law family of a solution lies in $\mathcal M$. Each $\xi^n$ is assumed measurable (needed for the $n$-particle filtration). The conventions of the setting file apply: sup norm on $\mathbb R^d$, path-valued processes, natural filtrations, and lower Lebesgue integrals for expectations.
-- source:
--   Bayraktar, Chakraborty, Wu, Graphon mean field systems, Ann. Appl. Probab. 33(5) (2023), p. 3595, Theorem 3.1

import Mathlib
import Definitions.Def_GraphonMF_DenseLLN_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GraphonMF.DenseLLN
theorem theorem_3_1 {Ω : Type*} [MeasurableSpace Ω] {T : ℝ≥0} {d N : ℕ} {P : Measure Ω}
    {μ0 : GraphonMF.Stability.I → Measure (GraphonMF.Stability.State d)} {X0 : GraphonMF.Stability.I → Ω → GraphonMF.Stability.State d} {B : GraphonMF.Stability.I → ℝ≥0 → Ω → GraphonMF.Stability.State d}
    (noise : NoiseSetting P μ0 X0 B) (hT : 0 < T)
    (b : GraphonMF.Stability.State d → GraphonMF.Stability.State d → GraphonMF.Stability.State d) (σ : GraphonMF.Stability.State d → GraphonMF.Stability.State d → Matrix (Fin d) (Fin d) ℝ)
    (ε : ℝ) (h21 : GraphonMF.Stability.Cond21 ε μ0 b σ)
    (J : Fin N → Set GraphonMF.Stability.I) (h22a : Cond22a μ0 J)
    (G : GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ) (hG : GraphonMF.Stability.IsGraphon G)
    (Gs : ℕ → GraphonMF.Stability.I → GraphonMF.Stability.I → ℝ) (h31a : ∀ n, 0 < n → GraphonMF.Stability.IsStepGraphon n (Gs n))
    (ξ : (n : ℕ) → Ω → Fin n → Fin n → ℝ) (hξ : ∀ n, Measurable (ξ n))
    (h31b : Cond31b P X0 B ξ Gs)
    (h31c : Tendsto (fun n => GraphonMF.Stability.cutNorm (fun u v => Gs n u v - G u v)) atTop (𝓝 0))
    (X : GraphonMF.Stability.I → Ω → GraphonMF.Stability.Cd T d) (hX : IsGraphonSolution noise G b σ X)
    (Xn : (n : ℕ) → Fin n → Ω → GraphonMF.Stability.Cd T d)
    (hXn : ∀ n, IsParticleSolution noise b σ n (ξ n) (hξ n) (Xn n)) :
    TendstoInProb P (fun n ω => empiricalPM (fun i => Xn n i ω)) (mixturePM P X) ∧
      (Cond22b G J → Tendsto (fun n : ℕ => (1 / (n : ℝ≥0∞)) *
          ∑ i : Fin n, ∫⁻ ω, ‖Xn n i ω - X (GraphonMF.Stability.lab n i) ω‖ₑ ^ 2 ∂P) atTop (𝓝 0)) := by sorry
end GraphonMF.DenseLLN
