-- Prove2me | Theorems.Thm_FunctionalInequalities_L2_integral_affine_sq_408915f
-- name    : FunctionalInequalities.L2.integral_affine_sq_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:31:30.834853+00:00
-- url     : https://prove2.me/theorems/914a2c50-85d6-424f-9c86-5daf983db7cd
-- title:
--   Square Integral of an Affine Function Under Isotropic Moment Conditions
-- statement:
--   This statement evaluates the square integral of an affine function under centered identity-covariance moment assumptions.
--
--   Let $n\in\mathbb N$, $E=$ `EuclideanSpace ℝ (Fin n)`, and $e_j=$ `EuclideanSpace.basisFun (Fin n) ℝ j`. Assume:
--
--   1. $\mu$ is a probability measure and $\operatorname{id}\in L^2(\mu)$ (`MemLp`).
--   2. $\int x\,d\mu(x)=0$.
--   3. For every $u,v\in E$, $\int\langle u,x\rangle\langle v,x\rangle\,d\mu(x)=\langle u,v\rangle$.
--
--   For every $c\in\mathbb R$ and coefficient family $a:\operatorname{Fin}(n)\to\mathbb R$,
--   $$
--   \int\left(c+\sum_{j\in\operatorname{Fin}(n)}a_j\langle e_j,x\rangle\right)^2\,d\mu(x)
--   =c^2+\sum_{j\in\operatorname{Fin}(n)}a_j^2.
--   $$
--   This identifies the $L^2$ square of the affine part with the Euclidean square of its coefficients. No log-concavity or positive-dimension assumption is needed.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/L2/AffineDecomposition.lean#L880-L935 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.L2.AffineDecomposition`, declaration `FunctionalInequalities.L2.integral_affine_sq`; the repository is private at upload time).

import Definitions.Def_KLS408915f_FunctionalInequalities_L2_AffineDecomposition
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory
open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.L2
end FunctionalInequalities.L2
open FunctionalInequalities FunctionalInequalities.L2
section AffineOrthPart
variable {n : ℕ}

theorem FunctionalInequalities.L2.integral_affine_sq_408915f (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsProbabilityMeasure μ]
    (hμ2 : MemLp id 2 μ) (hμ0 : ∫ x, x ∂μ = 0)
    (hμcov : ∀ u v : EuclideanSpace ℝ (Fin n), ∫ x, ⟪u, x⟫ * ⟪v, x⟫ ∂μ = ⟪u, v⟫)
    (c : ℝ) (a : Fin n → ℝ) :
    ∫ x, (c + ∑ j, a j * ⟪EuclideanSpace.basisFun (Fin n) ℝ j, x⟫) ^ 2 ∂μ =
      c ^ 2 + ∑ j, a j ^ 2 := by sorry
