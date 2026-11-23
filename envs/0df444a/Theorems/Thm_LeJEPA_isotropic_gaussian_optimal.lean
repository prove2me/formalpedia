-- Prove2me | Theorems.Thm_LeJEPA_isotropic_gaussian_optimal
-- name    : LeJEPA.isotropic_gaussian_optimal
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-23T11:43:58.070736+00:00
-- url     : https://prove2.me/theorems/dcd49524-9ee5-41af-b3d4-1b7037b1edea
-- title:
--   Isotropic Gaussian optimality: the isotropic Gaussian uniquely minimises the Fisher information under a scalar covariance constraint
-- statement:
--   Let $K\ge1$. Among mean-zero, continuously differentiable probability densities $p$ on $\mathbb{R}^K$ with finite second moments and positive-definite covariance $\Sigma$, the Fisher information $J(p)=\int\|\nabla\log p\|^2p$ is minimised under each of the following scalar covariance constraints by an isotropic Gaussian $\mathcal N(0,sI_K)$, and by it alone.
--
--   | constraint | minimal $J$ | minimiser |
--   |---|---|---|
--   | $\operatorname{tr}\Sigma=t$ | $K^2/t$ | $s=t/K$ |
--   | $\det\Sigma=\delta$ | $K\delta^{-1/K}$ | $s=\delta^{1/K}$ |
--   | $\|\Sigma\|_F=c$ | $K^{3/2}/c$ | $s=c/\sqrt K$ |
--   | $\rho(\Sigma)\le r$ | $K/r$ | $s=r$ |
--
--   Precisely, for each constraint with parameter $t,\delta,c,r>0$:
--
--   1. the minimiser is an admissible density, has covariance $sI_K$, and has Fisher information equal to the minimal value;
--   2. every admissible $p$ satisfying the constraint has $J(p)$ at least the minimal value;
--   3. equality holds only for the minimiser.
--
--   Here $\rho(\Sigma)$ is the largest eigenvalue of $\Sigma$. In the paper this is what makes the isotropic Gaussian the optimal distribution for embeddings: the leading bias of $k$-NN and kernel probes is proportional to $J(p)$ (Theorems 1, 7 and 8), so under a fixed covariance budget the isotropic Gaussian minimises it.
--
--   **Formalization Note** $J$ takes values in $[0,\infty]$; densities without finite Fisher information satisfy the inequality trivially. Uniqueness is stated pointwise, which is the same as uniqueness up to null sets here because admissible densities are continuous.
-- source:
--   Balestriero and LeCun, LeJEPA: Provable and Scalable Self-Supervised Learning Without the Heuristics, arXiv:2511.08544v3 (2025), Appendix B.4, Theorem 9 (stated in the proof of Theorem 7); it is the precise form of the uniqueness claim of Theorem 1 (Section 3.2) and Theorem 7 (Appendix A.1)

import Mathlib
import Definitions.Def_LeJEPA_Basic

open MeasureTheory Matrix Filter Topology
open scoped ENNReal InnerProductSpace

namespace LeJEPA

theorem isotropic_gaussian_optimal {K : ℕ} (hK : 0 < K) :
    -- (a) trace constraint tr Σ = t
    (∀ t : ℝ, 0 < t →
      IsMeanZeroDensity (gaussDensity ((t / K) • (1 : Matrix (Fin K) (Fin K) ℝ))) ∧
      covMat (gaussDensity ((t / K) • (1 : Matrix (Fin K) (Fin K) ℝ))) = (t / K) • 1 ∧
      fisherInfo (gaussDensity ((t / K) • (1 : Matrix (Fin K) (Fin K) ℝ))) = ENNReal.ofReal ((K : ℝ) ^ 2 / t) ∧
      ∀ p : (Fin K → ℝ) → ℝ, IsMeanZeroDensity p → (covMat p).PosDef → (covMat p).trace = t →
        ENNReal.ofReal ((K : ℝ) ^ 2 / t) ≤ fisherInfo p ∧
        (fisherInfo p = ENNReal.ofReal ((K : ℝ) ^ 2 / t) ↔ p = gaussDensity ((t / K) • 1))) ∧
    -- (b) determinant constraint det Σ = δ
    (∀ δ : ℝ, 0 < δ →
      IsMeanZeroDensity (gaussDensity (δ ^ (1 / (K : ℝ)) • (1 : Matrix (Fin K) (Fin K) ℝ))) ∧
      covMat (gaussDensity (δ ^ (1 / (K : ℝ)) • (1 : Matrix (Fin K) (Fin K) ℝ))) = δ ^ (1 / (K : ℝ)) • 1 ∧
      fisherInfo (gaussDensity (δ ^ (1 / (K : ℝ)) • (1 : Matrix (Fin K) (Fin K) ℝ))) =
        ENNReal.ofReal (K * δ ^ (-(1 / (K : ℝ)))) ∧
      ∀ p : (Fin K → ℝ) → ℝ, IsMeanZeroDensity p → (covMat p).PosDef → (covMat p).det = δ →
        ENNReal.ofReal (K * δ ^ (-(1 / (K : ℝ)))) ≤ fisherInfo p ∧
        (fisherInfo p = ENNReal.ofReal (K * δ ^ (-(1 / (K : ℝ)))) ↔ p = gaussDensity (δ ^ (1 / (K : ℝ)) • 1))) ∧
    -- (c) Frobenius constraint ‖Σ‖_F = c
    (∀ c : ℝ, 0 < c →
      IsMeanZeroDensity (gaussDensity ((c / Real.sqrt K) • (1 : Matrix (Fin K) (Fin K) ℝ))) ∧
      covMat (gaussDensity ((c / Real.sqrt K) • (1 : Matrix (Fin K) (Fin K) ℝ))) = (c / Real.sqrt K) • 1 ∧
      fisherInfo (gaussDensity ((c / Real.sqrt K) • (1 : Matrix (Fin K) (Fin K) ℝ))) =
        ENNReal.ofReal ((K : ℝ) ^ ((3 : ℝ) / 2) / c) ∧
      ∀ p : (Fin K → ℝ) → ℝ, IsMeanZeroDensity p → (covMat p).PosDef → frobNorm (covMat p) = c →
        ENNReal.ofReal ((K : ℝ) ^ ((3 : ℝ) / 2) / c) ≤ fisherInfo p ∧
        (fisherInfo p = ENNReal.ofReal ((K : ℝ) ^ ((3 : ℝ) / 2) / c) ↔ p = gaussDensity ((c / Real.sqrt K) • 1))) ∧
    -- (d) spectral-radius bound ρ(Σ) ≤ r
    (∀ r : ℝ, 0 < r →
      IsMeanZeroDensity (gaussDensity (r • (1 : Matrix (Fin K) (Fin K) ℝ))) ∧
      covMat (gaussDensity (r • (1 : Matrix (Fin K) (Fin K) ℝ))) = r • 1 ∧
      fisherInfo (gaussDensity (r • (1 : Matrix (Fin K) (Fin K) ℝ))) = ENNReal.ofReal (K / r) ∧
      ∀ p : (Fin K → ℝ) → ℝ, IsMeanZeroDensity p → ∀ hcov : (covMat p).PosDef,
        (∀ i, hcov.isHermitian.eigenvalues i ≤ r) →
        ENNReal.ofReal (K / r) ≤ fisherInfo p ∧
        (fisherInfo p = ENNReal.ofReal (K / r) ↔ p = gaussDensity (r • 1))) := by sorry

end LeJEPA
