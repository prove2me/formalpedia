-- Prove2me | Theorems.Thm_GraphonMF_SparseRate_eq_7_2
-- name    : GraphonMF.SparseRate.eq_7_2
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-04T22:18:32.445633+00:00
-- url     : https://prove2.me/theorems/ca8c6501-71eb-4c6f-aad7-1a7ce713f58a
-- title:
--   (7.2), p. 3611 — the drift error splits as 4(R^{n,1}_s + R^{n,2}_s + R^{n,3}_s + R^{n,4}_s)
-- statement:
--   For every $n$, every solution $X^n$ of (4.1) and every $s\in[0,T]$,
--   $$\frac1n\sum_{i=1}^n\mathbb E\Big|\frac1{n\beta_n}\sum_{j=1}^n\xi^n_{ij}\,b(X^n_i(s),X^n_j(s))-\int_I\int_{\mathbb R^d}b(X_{i/n}(s),x)\,G(i/n,v)\,\mu_{v,s}(dx)\,dv\Big|^2\le4\big(R^{n,1}_s+R^{n,2}_s+R^{n,3}_s+R^{n,4}_s\big),$$
--   where
--   $$R^{n,1}_s=\frac1n\sum_{i=1}^n\mathbb E\Big|\frac1n\sum_{j=1}^n\frac{\xi^n_{ij}}{\beta_n}\big(b(X^n_i(s),X^n_j(s))-b(X_{i/n}(s),X^n_j(s))\big)\Big|^2,$$
--   $$R^{n,2}_s=\frac1n\sum_{i=1}^n\mathbb E\Big|\frac1n\sum_{j=1}^n\frac{\xi^n_{ij}}{\beta_n}\big(b(X_{i/n}(s),X^n_j(s))-b(X_{i/n}(s),X_{j/n}(s))\big)\Big|^2,$$
--   $$R^{n,3}_s=\frac1n\sum_{i=1}^n\mathbb E\Big|\frac1n\sum_{j=1}^n\Big(\frac{\xi^n_{ij}}{\beta_n}b(X_{i/n}(s),X_{j/n}(s))-\int_{\mathbb R^d}b(X_{i/n}(s),x)\,G(\tfrac in,\tfrac jn)\,\mu_{j/n,s}(dx)\Big)\Big|^2,$$
--   $$R^{n,4}_s=\frac1n\sum_{i=1}^n\mathbb E\Big|\frac1n\sum_{j=1}^n\int_{\mathbb R^d}b(X_{i/n}(s),x)\,G(\tfrac in,\tfrac jn)\,\mu_{j/n,s}(dx)-\int_I\int_{\mathbb R^d}b(X_{i/n}(s),x)\,G(\tfrac in,v)\,\mu_{v,s}(dx)\,dv\Big|^2.$$
--
--   This is the add-and-subtract decomposition (7.2) of the paper, with $G_n(i/n,j/n)$ replaced by $G(i/n,j/n)$ as is appropriate under Condition 4.3 (§7.3); the four differences sum to the drift error, and $|a_1+a_2+a_3+a_4|^2\le4\sum_k|a_k|^2$. $R^{n,2}_s$ and $R^{n,4}_s$ are the terms `Rn2`, `Rn4` of the setting.
--
--   Throughout, $\{B_u,X_u(0):u\in I\}$ is the continuum noise, $b$, $\sigma$, $\beta_n$ satisfy Condition 4.1, $G$ is a graphon, the edges $\xi^n_{ij}=\xi^n_{ji}\sim\mathrm{Bernoulli}(\beta_nG(i/n,j/n))$ are independent for $i\le j$ and independent of the noise (Condition 4.3), $X=(X_u)_{u\in I}$ solves the graphon limit system (4.2) with $\mu_{v,s}=\mathcal L(X_v(s))$, and $X^n=(X^n_i)_{i\le n}$ is any solution of the not-so-dense system (4.1), $dX^n_i=\frac1{n\beta_n}\sum_j\xi^n_{ij}b(X^n_i,X^n_j)\,ds+\sigma(X^n_i)\,dB_{i/n}$, $X^n_i(0)=X_{i/n}(0)$. Expectations are lower Lebesgue integrals in $[0,\infty]$; the solution concepts are those of the `GraphonMF_SparseRate_Setting` definitions.
-- source:
--   Bayraktar, Chakraborty, Wu, Graphon mean field systems, Ann. Appl. Probab. 33(5) (2023), p. 3611, (7.2) (arXiv:2003.13180 v3, p. 26); with G in place of G_n under Condition 4.3: p. 3616, §7.3

import Mathlib
import Definitions.Def_GraphonMF_SparseRate_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GraphonMF.SparseRate

/-- (7.2) (p. 3611), with `G` in place of `Gₙ` as under Condition 4.3 (§7.3, p. 3616): for every `n`, every
solution `Xⁿ` of (4.1) and every `s ≤ T`, the drift error of (7.1) is at most `4(R^{n,1}_s + R^{n,2}_s + R^{n,3}_s + R^{n,4}_s)`. -/
theorem eq_7_2 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ} {T : ℝ≥0} (hT : 0 < T)
    {μ0 : I → Measure (Fin d → ℝ)} {X0 : I → Ω → Fin d → ℝ} {B : I → ℝ≥0 → Ω → Fin d → ℝ}
    (hN : NoiseSetting P μ0 X0 B)
    {b : (Fin d → ℝ) → (Fin d → ℝ) → (Fin d → ℝ)} {σ : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ}
    {β : ℕ → ℝ} (h41 : Cond41 μ0 b σ β) {G : I → I → ℝ} (hG : GraphonMF.DenseRate.IsGraphon G)
    {ξ : (n : ℕ) → Ω → Fin n → Fin n → ℝ} (h43 : Cond43 P X0 B ξ β G)
    {X : I → ℝ≥0 → Ω → Fin d → ℝ} (hX : IsGraphonSolution42 P hN T b σ G X) :
    ∀ (n : ℕ) (Xn : Fin n → ℝ≥0 → Ω → Fin d → ℝ),
      IsParticleSolution41 P hN h43.meas T b σ β n Xn → ∀ s : ℝ≥0, s ≤ T →
        (1 / (n : ℝ≥0∞)) * ∑ i : Fin n, ∫⁻ ω,
            ‖(1 / ((n : ℝ) * β n)) • ∑ j : Fin n, ξ n ω i j • b (Xn i s ω) (Xn j s ω) -
              driftAvg P b G X (GraphonMF.DenseRate.lab n i) s (X (GraphonMF.DenseRate.lab n i) s ω)‖ₑ ^ 2 ∂P ≤
          4 * (((1 / (n : ℝ≥0∞)) * ∑ i : Fin n, ∫⁻ ω,
            ‖(1 / (n : ℝ)) • ∑ j : Fin n, (ξ n ω i j / β n) •
              (b (Xn i s ω) (Xn j s ω) - b (X (GraphonMF.DenseRate.lab n i) s ω) (Xn j s ω))‖ₑ ^ 2 ∂P) + Rn2 P b β ξ X n Xn s + ((1 / (n : ℝ≥0∞)) * ∑ i : Fin n, ∫⁻ ω,
            ‖(1 / (n : ℝ)) • ∑ j : Fin n, ((ξ n ω i j / β n) • b (X (GraphonMF.DenseRate.lab n i) s ω) (X (GraphonMF.DenseRate.lab n j) s ω) -
              G (GraphonMF.DenseRate.lab n i) (GraphonMF.DenseRate.lab n j) • ∫ x, b (X (GraphonMF.DenseRate.lab n i) s ω) x ∂(P.map (X (GraphonMF.DenseRate.lab n j) s)))‖ₑ ^ 2 ∂P) + Rn4 P b G X n s) := by sorry

end GraphonMF.SparseRate
