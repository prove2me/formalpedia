-- Prove2me | Theorems.Thm_GraphonMF_SparseRate_eq_7_1
-- name    : GraphonMF.SparseRate.eq_7_1
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-04T22:18:55.522416+00:00
-- url     : https://prove2.me/theorems/5e9e2661-0434-46f4-b186-7739a2794b1a
-- title:
--   (7.1), p. 3611 — Itô/Doob estimate of (1/n)Σᵢ𝔼‖Xⁿᵢ − X_{i/n}‖²_{*,t} by the drift error and the coupling error
-- statement:
--   There is $\kappa\in\mathbb R$ such that for every $n$, every solution $X^n$ of (4.1) and every $t\in[0,T]$,
--   $$\frac1n\sum_{i=1}^n\mathbb E\|X^n_i-X_{i/n}\|^2_{*,t}\le\kappa\int_0^t\frac1n\sum_{i=1}^n\mathbb E\Big|\frac1{n\beta_n}\sum_{j=1}^n\xi^n_{ij}\,b(X^n_i(s),X^n_j(s))-\int_I\int_{\mathbb R^d}b(X_{i/n}(s),x)\,G(i/n,v)\,\mu_{v,s}(dx)\,dv\Big|^2ds+\kappa\int_0^t\frac1n\sum_{i=1}^n\mathbb E\big|X^n_i(s)-X_{i/n}(s)\big|^2ds.$$
--
--   Here $\|x-y\|_{*,t}=\sup_{0\le s\le t}|x(s)-y(s)|$. This is (7.1) of the paper, which §7.3 states remains valid under Conditions 4.1 and 4.3; it follows from the common initial condition and Brownian motion of $X^n_i$ and $X_{i/n}$, the Cauchy–Schwarz inequality for the drift part, Doob's $L^2$ maximal inequality for the stochastic integral and the Lipschitz property of $\sigma$.
--
--   Throughout, $\{B_u,X_u(0):u\in I\}$ is the continuum noise, $b$, $\sigma$, $\beta_n$ satisfy Condition 4.1, $G$ is a graphon, the edges $\xi^n_{ij}=\xi^n_{ji}\sim\mathrm{Bernoulli}(\beta_nG(i/n,j/n))$ are independent for $i\le j$ and independent of the noise (Condition 4.3), $X=(X_u)_{u\in I}$ solves the graphon limit system (4.2) with $\mu_{v,s}=\mathcal L(X_v(s))$, and $X^n=(X^n_i)_{i\le n}$ is any solution of the not-so-dense system (4.1), $dX^n_i=\frac1{n\beta_n}\sum_j\xi^n_{ij}b(X^n_i,X^n_j)\,ds+\sigma(X^n_i)\,dB_{i/n}$, $X^n_i(0)=X_{i/n}(0)$. Expectations are lower Lebesgue integrals in $[0,\infty]$; the solution concepts are those of the `GraphonMF_SparseRate_Setting` definitions.
-- source:
--   Bayraktar, Chakraborty, Wu, Graphon mean field systems, Ann. Appl. Probab. 33(5) (2023), p. 3611, (7.1) (arXiv:2003.13180 v3, p. 26); validity under Conditions 4.1 and 4.3: p. 3616, §7.3, first sentence

import Mathlib
import Definitions.Def_GraphonMF_SparseRate_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GraphonMF.SparseRate

/-- (7.1) (p. 3611), valid under Conditions 4.1 and 4.3 (§7.3, p. 3616): there is `κ` such that for all `n`, all
solutions `Xⁿ` of (4.1) and all `t ≤ T`,
`(1/n) Σᵢ 𝔼‖Xⁿᵢ − X_{i/n}‖²_{*,t} ≤ κ ∫₀ᵗ (1/n) Σᵢ 𝔼|(1/(nβₙ)) Σⱼ ξⁿᵢⱼ b(Xⁿᵢ(s), Xⁿⱼ(s)) − ∫_I∫ b(X_{i/n}(s), x) G(i/n, v) μ_{v,s}(dx) dv|² ds
+ κ ∫₀ᵗ (1/n) Σᵢ 𝔼|Xⁿᵢ(s) − X_{i/n}(s)|² ds`. -/
theorem eq_7_1 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ} {T : ℝ≥0} (hT : 0 < T)
    {μ0 : I → Measure (Fin d → ℝ)} {X0 : I → Ω → Fin d → ℝ} {B : I → ℝ≥0 → Ω → Fin d → ℝ}
    (hN : NoiseSetting P μ0 X0 B)
    {b : (Fin d → ℝ) → (Fin d → ℝ) → (Fin d → ℝ)} {σ : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ}
    {β : ℕ → ℝ} (h41 : Cond41 μ0 b σ β) {G : I → I → ℝ} (hG : GraphonMF.DenseRate.IsGraphon G)
    {ξ : (n : ℕ) → Ω → Fin n → Fin n → ℝ} (h43 : Cond43 P X0 B ξ β G)
    {X : I → ℝ≥0 → Ω → Fin d → ℝ} (hX : IsGraphonSolution42 P hN T b σ G X) : 
    ∃ κ : ℝ, ∀ (n : ℕ) (Xn : Fin n → ℝ≥0 → Ω → Fin d → ℝ),
      IsParticleSolution41 P hN h43.meas T b σ β n Xn → ∀ t : ℝ≥0, t ≤ T →
        (1 / (n : ℝ≥0∞)) * ∑ i : Fin n,
            ∫⁻ ω, GraphonMF.DenseRate.supDistUpTo t (Xn i) (X (GraphonMF.DenseRate.lab n i)) ω ^ 2 ∂P ≤
          ENNReal.ofReal κ * (∫⁻ s in Set.Icc (0 : ℝ) t, (1 / (n : ℝ≥0∞)) * ∑ i : Fin n, ∫⁻ ω,
              ‖(1 / ((n : ℝ) * β n)) • ∑ j : Fin n, ξ n ω i j • b (Xn i s.toNNReal ω) (Xn j s.toNNReal ω) -
                driftAvg P b G X (GraphonMF.DenseRate.lab n i) s.toNNReal (X (GraphonMF.DenseRate.lab n i) s.toNNReal ω)‖ₑ ^ 2 ∂P) +
          ENNReal.ofReal κ * (∫⁻ s in Set.Icc (0 : ℝ) t, (1 / (n : ℝ≥0∞)) * ∑ i : Fin n, ∫⁻ ω,
              ‖Xn i s.toNNReal ω - X (GraphonMF.DenseRate.lab n i) s.toNNReal ω‖ₑ ^ 2 ∂P) := by sorry

end GraphonMF.SparseRate
