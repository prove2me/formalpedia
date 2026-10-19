-- Prove2me | Theorems.Thm_LocalDistanceNetwork_variance_linear_estimator
-- name    : LocalDistanceNetwork.variance_linear_estimator
-- status  : Proved
-- author  : @Lucas
-- created : 2026-10-12T20:25:51.067901+00:00
-- url     : https://prove2.me/theorems/c2ac9697-c831-441c-9cd7-19d212cdbadd
-- title:
--   Variance of a linear estimate: $\operatorname{Var}(v^{\mathsf T}LY)=v^{\mathsf T}LCL^{\mathsf T}v$
-- statement:
--   Let $(\Omega,\mathcal F,\mu)$ be a probability space and let $\varepsilon=(\varepsilon_1,\dots,\varepsilon_m)$ be a random vector whose components are square integrable, with covariances $\operatorname{Cov}(\varepsilon_i,\varepsilon_j)=C_{ij}$ for a matrix $C\in\mathbb R^{m\times m}$. Let $Y=AX_0+\varepsilon$ for a matrix $A\in\mathbb R^{m\times n}$ and a vector $X_0\in\mathbb R^{n}$. Then for every matrix $L\in\mathbb R^{n\times m}$ and every vector $v\in\mathbb R^{n}$,
--   $$
--   \operatorname{Var}\big(v^{\mathsf T}LY\big)=v^{\mathsf T}\,\big(L\,C\,L^{\mathsf T}\big)\,v .
--   $$
--
--   This connects the matrix $LCL^{\mathsf T}$ used in the matrix-form statements with the variance of the random estimate $LY$, so that Loewner-order comparisons of covariance matrices become comparisons of variances.
-- source:
--   H0DN Collaboration (S. Casertano et al.), The Local Distance Network: A community consensus report on the measurement of the Hubble constant at ~1% precision, A&A 708, A166 (2026), https://doi.org/10.1051/0004-6361/202557993, Appendix B (p. 34) and Appendix B.2 (pp. 34-35), Eqs. (B.1)-(B.2)

import Mathlib
import Definitions.Def_LocalDistanceNetwork_GLS

open Matrix
open MeasureTheory ProbabilityTheory

namespace LocalDistanceNetwork
theorem variance_linear_estimator {m n : Type*} [Fintype m] [Fintype n]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (C : Matrix m m ℝ) (ε : Ω → m → ℝ)
    (hε : ∀ i, MemLp (fun ω => ε ω i) 2 μ)
    (hcov : ∀ i j, cov[fun ω => ε ω i, fun ω => ε ω j; μ] = C i j)
    (A : Matrix m n ℝ) (X₀ : n → ℝ) (L : Matrix n m ℝ) (v : n → ℝ) :
    Var[fun ω => v ⬝ᵥ (L *ᵥ (A *ᵥ X₀ + ε ω)); μ] = v ⬝ᵥ (linearEstimatorCov L C *ᵥ v) := by sorry
end LocalDistanceNetwork
