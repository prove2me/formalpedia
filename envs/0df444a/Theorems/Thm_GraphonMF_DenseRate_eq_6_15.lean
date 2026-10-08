-- Prove2me | Theorems.Thm_GraphonMF_DenseRate_eq_6_15
-- name    : GraphonMF.DenseRate.eq_6_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:28:21.058024+00:00
-- url     : https://prove2.me/theorems/1a97a83d-211d-4054-9ce3-1ea97fb3c991
-- title:
--   (6.15), pp. 3608–3609 — E‖Xⁿ_i − X_{i/n}‖²_{*,t} ≤ κ E∫₀ᵗ (|drift mismatch|² + |diffusion mismatch|²) ds
-- statement:
--   Work in the setting of Theorem 3.2 of Bayraktar–Chakraborty–Wu: a graphon $G$, coefficients $b,\sigma$ satisfying Condition 2.1, edge weights $\xi^n_{ij}$ satisfying Condition 3.2, a solution $X=(X_u)_{u\in I}$ of the graphon particle system (2.1) with $\mu_{v,s}=\mathcal L(X_v(s))$, and, for each $n$, a solution $X^n$ of the $n$-particle system (3.1), where particle $i$ starts at $X_{i/n}(0)$ and is driven by $B_{i/n}$.
--
--   There is a constant $\kappa\in(0,\infty)$, independent of $n$, $i$ and $t$, such that for every $n$, every $i\in\{1,\dots,n\}$ and every $t\in[0,T]$,
--   $$\mathbb E\|X^n_i-X_{i/n}\|^2_{*,t}\le\kappa\,\mathbb E\int_0^t\Big|\frac1n\sum_{j=1}^n\xi^n_{ij}b(X^n_i(s),X^n_j(s))-\int_I\!\int_{\mathbb R^d}b(X_{i/n}(s),x)G(\tfrac in,v)\mu_{v,s}(dx)\,dv\Big|^2ds$$
--   $$\qquad+\kappa\,\mathbb E\int_0^t\Big|\frac1n\sum_{j=1}^n\xi^n_{ij}\sigma(X^n_i(s),X^n_j(s))-\int_I\!\int_{\mathbb R^d}\sigma(X_{i/n}(s),x)G(\tfrac in,v)\mu_{v,s}(dx)\,dv\Big|^2ds.$$
--
--   Because the $i$-th particle and the continuum particle at $u=i/n$ share their initial state and Brownian motion, their difference consists of a drift mismatch and a stochastic integral of the diffusion mismatch only; this display is the starting point of the Gronwall argument for Theorem 3.2.
--
--   **Formalization Note.** The time integral is a lower Lebesgue integral over $[0,t]\subset\mathbb R$, the expectation a lower integral over $\Omega$; the matrix mismatch is measured entrywise (max norm). The hypotheses are those of Theorem 3.2 that the display uses (Condition 2.3 is not needed and not assumed).
-- source:
--   Bayraktar, Chakraborty, Wu, Graphon mean field systems, Ann. Appl. Probab. 33(5) (2023), https://doi.org/10.1214/22-AAP1901, pp. 3608–3609, §6.3, (6.15)

import Mathlib
import Definitions.Def_GraphonMF_DenseRate_Setting

open MeasureTheory ProbabilityTheory Filter Topology unitInterval
open scoped ENNReal NNReal

namespace GraphonMF.DenseRate

theorem eq_6_15 {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} (T : ℝ≥0) (hT : 0 < T)
    (P : Measure Ω) (μ0 : I → Measure (Fin d → ℝ)) (X0 : I → Ω → (Fin d → ℝ))
    (B : I → ℝ≥0 → Ω → Fin d → ℝ) (hN : NoiseSetting P μ0 X0 B)
    (ξ : (n : ℕ) → Ω → Fin n → Fin n → ℝ)
    (b : (Fin d → ℝ) → (Fin d → ℝ) → (Fin d → ℝ))
    (sigma : (Fin d → ℝ) → (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℝ)
    (ε : ℝ) (hε : 0 < ε) (h21 : Cond21 ε μ0 b sigma)
    (G : I → I → ℝ) (hG : IsGraphon G)
    (h32 : Cond32 P X0 B ξ G)
    (X : I → ℝ≥0 → Ω → (Fin d → ℝ)) (hX : IsGraphonSolution T P X0 B G b sigma X) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (n : ℕ) (Xn : Fin n → ℝ≥0 → Ω → (Fin d → ℝ)),
      IsParticleSolution T P X0 B ξ b sigma n Xn → ∀ (i : Fin n) (t : ℝ≥0), t ≤ T →
      ∫⁻ ω, supDistUpTo t (Xn i) (X (lab n i)) ω ^ 2 ∂P ≤
        ENNReal.ofReal κ * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
          ‖(1 / (n : ℝ)) • ∑ j, ξ n ω i j • b (Xn i s.toNNReal ω) (Xn j s.toNNReal ω) -
            graphonDrift P G b X (lab n i) s.toNNReal (X (lab n i) s.toNNReal ω)‖ₑ ^ 2 ∂volume ∂P
        + ENNReal.ofReal κ * ∫⁻ ω, ∫⁻ s in Set.Icc (0 : ℝ) t,
          ‖fun p : Fin d × Fin d =>
            (1 / (n : ℝ)) * ∑ j, ξ n ω i j * sigma (Xn i s.toNNReal ω) (Xn j s.toNNReal ω) p.1 p.2 -
              graphonDiff P G sigma X (lab n i) s.toNNReal (X (lab n i) s.toNNReal ω) p.1 p.2‖ₑ ^ 2
            ∂volume ∂P := by sorry

end GraphonMF.DenseRate
