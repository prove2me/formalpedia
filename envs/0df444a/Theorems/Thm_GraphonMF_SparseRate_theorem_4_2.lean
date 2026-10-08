-- Prove2me | Theorems.Thm_GraphonMF_SparseRate_theorem_4_2
-- name    : GraphonMF.SparseRate.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T07:43:55.95539+00:00
-- url     : https://prove2.me/theorems/fb6337b5-b4b6-4c42-b080-dbc7f4efde50
-- title:
--   Theorem 4.2, p. 3598 — (1/n) Σᵢ 𝔼‖Xⁿ_i − X_{i/n}‖²_{*,T} ≤ κ(q)/(nβₙ)^{1/q} for all n, for each q > 1
-- statement:
--   Let $\{B_u,X_u(0):u\in I\}$ be the continuum noise, with initial laws $\mu_u(0)$. Let $b:\mathbb R^d\times\mathbb R^d\to\mathbb R^d$, $\sigma:\mathbb R^d\to\mathbb R^{d\times d}$ and $\beta_n$ satisfy Condition 4.1, let $G$ be a graphon, and suppose Condition 2.3 holds (Lipschitz initial laws and Lipschitz graphon on finitely many blocks). Let the edges $\xi^n_{ij}=\xi^n_{ji}\sim\mathrm{Bernoulli}(\beta_nG(i/n,j/n))$ be independent for $i\le j$ and independent of the noise (Condition 4.3). Let $X=(X_u)_{u\in I}$ solve the limit system (4.2). Then for each $q\in(1,\infty)$ there is $\kappa(q)\in(0,\infty)$ such that for every $n\in\mathbb N$ and every solution $(X^n_i)_{i\le n}$ of the not-so-dense system (4.1), driven by the same $X_{i/n}(0)$ and $B_{i/n}$,
--   $$\frac1n\sum_{i=1}^n\mathbb E\big\|X^n_i-X_{i/n}\big\|_{*,T}^2\le\frac{\kappa(q)}{(n\beta_n)^{1/q}} .$$
--
--   On percolated graphs of sparsity $\beta_n$ sampled from a Lipschitz graphon, the average mean-square distance between each particle and its graphon limit therefore decays at the rate $(n\beta_n)^{-1/q}$ for every $q>1$, i.e. at almost the rate $1/(n\beta_n)$ of the effective number of neighbours.
--
--   **Formalization Note** The constant $\kappa(q)$ is chosen after $q$ and before $n$. At $n=0$ both sides are $0$ in Lean (an empty average, and $\kappa(q)/0=0$), so the statement is the paper's for $n\ge1$. The coupling of $X^n_i$ and $X_{i/n}$ through the same initial state and Brownian motion is the paper's model (1.1). $\|\cdot\|_{*,T}$ is the sup norm of $\mathcal C_d$ built on the sup norm of $\mathbb R^d$; expectations are lower Lebesgue integrals in $[0,\infty]$. The solution concepts and conventions are those of the `Setting` definitions.
-- source:
--   Bayraktar, Chakraborty, Wu, Graphon mean field systems, Ann. Appl. Probab. 33(5) (2023), p. 3598, Theorem 4.2, (4.5); proof in §7.3, pp. 3616–3617

import Mathlib
import Definitions.Def_GraphonMF_SparseRate_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GraphonMF.SparseRate

/-- Theorem 4.2 (p. 3598): under Conditions 2.3, 4.1 and 4.3, for each `q ∈ (1, ∞)` there is
`κ(q) ∈ (0, ∞)` with `(1/n) Σ_i 𝔼‖Xⁿ_i − X_{i/n}‖²_{*,T} ≤ κ(q)/(nβ_n)^{1/q}` for all `n`. -/
theorem theorem_4_2 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ} {T : ℝ≥0} (hT : 0 < T)
    {μ0 : I → Measure (Fin d → ℝ)} {X0 : I → Ω → Fin d → ℝ} {B : I → ℝ≥0 → Ω → Fin d → ℝ}
    (hN : NoiseSetting P μ0 X0 B)
    {b : (Fin d → ℝ) → (Fin d → ℝ) → (Fin d → ℝ)} {σ : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ}
    {β : ℕ → ℝ} (h41 : Cond41 μ0 b σ β) {G : I → I → ℝ} (hG : GraphonMF.DenseRate.IsGraphon G)
    {ξ : (n : ℕ) → Ω → Fin n → Fin n → ℝ} (h43 : Cond43 P X0 B ξ β G)
    {X : I → ℝ≥0 → Ω → Fin d → ℝ} (hX : IsGraphonSolution42 P hN T b σ G X)
    {N : ℕ} {J : Fin N → Set I} (h23 : Cond23 μ0 G J) :
    ∀ q : ℝ, 1 < q → ∃ κq : ℝ, 0 < κq ∧ ∀ (n : ℕ) (Xn : Fin n → ℝ≥0 → Ω → Fin d → ℝ),
      IsParticleSolution41 P hN h43.meas T b σ β n Xn →
        (1 / (n : ℝ≥0∞)) * ∑ i : Fin n,
            ∫⁻ ω, ‖GraphonMF.DenseRate.pathOf T (Xn i) ω - GraphonMF.DenseRate.pathOf T (X (GraphonMF.DenseRate.lab n i)) ω‖ₑ ^ 2 ∂P ≤
          ENNReal.ofReal (κq / ((n : ℝ) * β n) ^ (1 / q)) := by sorry

end GraphonMF.SparseRate
