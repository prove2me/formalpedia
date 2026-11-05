-- Prove2me | Theorems.Thm_GraphonMF_SparseRate_eq_7_4
-- name    : GraphonMF.SparseRate.eq_7_4
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-04T22:18:30.642985+00:00
-- url     : https://prove2.me/theorems/085069b4-1ef7-4a29-993e-ff96fe71dbeb
-- title:
--   (7.4), p. 3612 — R^{n,3}_s ≤ κ/(nβₙ)
-- statement:
--   There is $\kappa\in\mathbb R$ such that for every $n$, every solution $X^n$ of (4.1) and every $s\in[0,T]$,
--   $$R^{n,3}_s\le\frac{\kappa}{n\beta_n},\qquad R^{n,3}_s=\frac1n\sum_{i=1}^n\mathbb E\Big|\frac1n\sum_{j=1}^n\Big(\frac{\xi^n_{ij}}{\beta_n}b(X_{i/n}(s),X_{j/n}(s))-\int_{\mathbb R^d}b(X_{i/n}(s),x)\,G(\tfrac in,\tfrac jn)\,\mu_{j/n,s}(dx)\Big)\Big|^2.$$
--
--   This is (7.4) of the paper, which §7.3 states remains valid under Conditions 4.1 and 4.3. It follows from the independence of the edges $\{\xi^n_{ij}\}$ from the processes $\{X_{j/n}\}$, the mutual independence of the $X_{j/n}$ (driven by independent noises), the boundedness of $b$, and a weak-LLN type variance computation.
--
--   Throughout, $\{B_u,X_u(0):u\in I\}$ is the continuum noise, $b$, $\sigma$, $\beta_n$ satisfy Condition 4.1, $G$ is a graphon, the edges $\xi^n_{ij}=\xi^n_{ji}\sim\mathrm{Bernoulli}(\beta_nG(i/n,j/n))$ are independent for $i\le j$ and independent of the noise (Condition 4.3), $X=(X_u)_{u\in I}$ solves the graphon limit system (4.2) with $\mu_{v,s}=\mathcal L(X_v(s))$, and $X^n=(X^n_i)_{i\le n}$ is any solution of the not-so-dense system (4.1), $dX^n_i=\frac1{n\beta_n}\sum_j\xi^n_{ij}b(X^n_i,X^n_j)\,ds+\sigma(X^n_i)\,dB_{i/n}$, $X^n_i(0)=X_{i/n}(0)$. Expectations are lower Lebesgue integrals in $[0,\infty]$; the solution concepts are those of the `GraphonMF_SparseRate_Setting` definitions.
-- source:
--   Bayraktar, Chakraborty, Wu, Graphon mean field systems, Ann. Appl. Probab. 33(5) (2023), p. 3612, (7.4) (arXiv:2003.13180 v3, p. 27); validity under Conditions 4.1 and 4.3: p. 3616, §7.3, first sentence

import Mathlib
import Definitions.Def_GraphonMF_SparseRate_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace GraphonMF.SparseRate

/-- (7.4) (p. 3612), valid under Conditions 4.1 and 4.3 (§7.3, p. 3616): there is `κ` such that
`R^{n,3}_s ≤ κ/(nβₙ)` for all `n`, all solutions `Xⁿ` of (4.1) and all `s ≤ T`, where
`R^{n,3}_s = (1/n) Σᵢ 𝔼|(1/n) Σⱼ ((ξⁿᵢⱼ/βₙ) b(X_{i/n}(s), X_{j/n}(s)) − ∫ b(X_{i/n}(s), x) G(i/n, j/n) μ_{j/n,s}(dx))|²`. -/
theorem eq_7_4 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {d : ℕ} {T : ℝ≥0} (hT : 0 < T)
    {μ0 : I → Measure (Fin d → ℝ)} {X0 : I → Ω → Fin d → ℝ} {B : I → ℝ≥0 → Ω → Fin d → ℝ}
    (hN : NoiseSetting P μ0 X0 B)
    {b : (Fin d → ℝ) → (Fin d → ℝ) → (Fin d → ℝ)} {σ : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ}
    {β : ℕ → ℝ} (h41 : Cond41 μ0 b σ β) {G : I → I → ℝ} (hG : GraphonMF.DenseRate.IsGraphon G)
    {ξ : (n : ℕ) → Ω → Fin n → Fin n → ℝ} (h43 : Cond43 P X0 B ξ β G)
    {X : I → ℝ≥0 → Ω → Fin d → ℝ} (hX : IsGraphonSolution42 P hN T b σ G X) :
    ∃ κ : ℝ, ∀ (n : ℕ) (Xn : Fin n → ℝ≥0 → Ω → Fin d → ℝ),
      IsParticleSolution41 P hN h43.meas T b σ β n Xn → ∀ s : ℝ≥0, s ≤ T →
        (1 / (n : ℝ≥0∞)) * ∑ i : Fin n, ∫⁻ ω,
            ‖(1 / (n : ℝ)) • ∑ j : Fin n, ((ξ n ω i j / β n) • b (X (GraphonMF.DenseRate.lab n i) s ω) (X (GraphonMF.DenseRate.lab n j) s ω) -
              G (GraphonMF.DenseRate.lab n i) (GraphonMF.DenseRate.lab n j) • ∫ x, b (X (GraphonMF.DenseRate.lab n i) s ω) x ∂(P.map (X (GraphonMF.DenseRate.lab n j) s)))‖ₑ ^ 2 ∂P ≤ ENNReal.ofReal (κ / ((n : ℝ) * β n)) := by sorry

end GraphonMF.SparseRate
