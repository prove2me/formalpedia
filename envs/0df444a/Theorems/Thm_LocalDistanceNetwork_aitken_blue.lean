-- Prove2me | Theorems.Thm_LocalDistanceNetwork_aitken_blue
-- name    : LocalDistanceNetwork.aitken_blue
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-12T20:34:24.352408+00:00
-- url     : https://prove2.me/theorems/0201750e-f344-4206-9f65-fbf705fb4836
-- title:
--   Aitken (1935) — the $\chi^2$ solution of the Distance Network is the Best Linear Unbiased Estimator
-- statement:
--   Consider the linear model of Appendix B: data $Y=AX_0+\varepsilon\in\mathbb R^{m}$, where $A\in\mathbb R^{m\times n}$ is a coefficient matrix of full column rank, $X_0\in\mathbb R^{n}$ is the true parameter vector, and $\varepsilon$ is a random noise vector on a probability space $(\Omega,\mathcal F,\mu)$ whose components are square integrable, have mean zero, and have covariance matrix $C\in\mathbb R^{m\times m}$, $\operatorname{Cov}(\varepsilon_i,\varepsilon_j)=C_{ij}$, assumed positive definite. Let
--   $$
--   \hat X=(A^{\mathsf T}C^{-1}A)^{-1}A^{\mathsf T}C^{-1}\,Y
--   $$
--   be the minimizer of $\chi^2=(Y-AX)^{\mathsf T}C^{-1}(Y-AX)$ (Eq. (B.1)). Then:
--
--   1. $\hat X$ is unbiased: $\mathbb E[\hat X_j]=(X_0)_j$ for every coordinate $j$;
--   2. $\hat X$ has minimal variance among linear unbiased estimators: if $L\in\mathbb R^{n\times m}$ is such that $LY$ is unbiased for every value of the true parameter, i.e. $\mathbb E\big[L(AX_1+\varepsilon)\big]=X_1$ for all $X_1\in\mathbb R^{n}$, then for every $v\in\mathbb R^{n}$
--   $$
--   \operatorname{Var}\big(v^{\mathsf T}\hat X\big)\le\operatorname{Var}\big(v^{\mathsf T}LY\big).
--   $$
--
--   This is the statement, invoked in Appendix B of the paper, that the generalized least-squares solution of the Distance Network is the Best Linear Unbiased Estimator (BLUE); in particular it applies to the coordinate $\log_{10}H_0$.
--
--   **Formalization Note** No Gaussianity is assumed: as in the classical theorem, only mean zero, finite second moments and the covariance matrix $C$ are used. "Best" is expressed through the variance of every linear functional $v^{\mathsf T}(\cdot)$, which is equivalent to the Loewner-order comparison of covariance matrices.
-- source:
--   H0DN Collaboration (S. Casertano et al.), The Local Distance Network: A community consensus report on the measurement of the Hubble constant at ~1% precision, A&A 708, A166 (2026), https://doi.org/10.1051/0004-6361/202557993, Appendix B (p. 34) and Appendix B.2 (pp. 34-35), Eqs. (B.1)-(B.2)

import Mathlib
import Definitions.Def_LocalDistanceNetwork_GLS

open Matrix
open MeasureTheory ProbabilityTheory

namespace LocalDistanceNetwork
theorem aitken_blue {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix m n ℝ) (hA : Function.Injective A.mulVec)
    (C : Matrix m m ℝ) (hC : C.PosDef)
    (ε : Ω → m → ℝ)
    (hε : ∀ i, MemLp (fun ω => ε ω i) 2 μ)
    (hmean : ∀ i, μ[fun ω => ε ω i] = 0)
    (hcov : ∀ i j, cov[fun ω => ε ω i, fun ω => ε ω j; μ] = C i j)
    (X₀ : n → ℝ) :
    (∀ j, μ[fun ω => glsEstimate A C⁻¹ (A *ᵥ X₀ + ε ω) j] = X₀ j) ∧
    ∀ L : Matrix n m ℝ,
      (∀ X₁ : n → ℝ, ∀ j, μ[fun ω => (L *ᵥ (A *ᵥ X₁ + ε ω)) j] = X₁ j) →
      ∀ v : n → ℝ,
        Var[fun ω => v ⬝ᵥ glsEstimate A C⁻¹ (A *ᵥ X₀ + ε ω); μ] ≤
          Var[fun ω => v ⬝ᵥ (L *ᵥ (A *ᵥ X₀ + ε ω)); μ] := by sorry
end LocalDistanceNetwork
