-- Prove2me | Theorems.Thm_OAI_Paper256_main_result
-- name    : OAI.Paper256.main_result
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:00.154146+00:00
-- url     : https://prove2.me/theorems/158a4fd6-d817-4ef3-8579-e7df43a33eec
-- statement:
--   The theorem states that, for the ambient real vector space of triples consisting of two real symmetric 4x4 matrices X and Z and a vector y in R^3, six things hold. First, this space has real dimension 23 (10+10+3). Second, a distinguished polynomial in these 23 coordinates, defined as det(det(X)·Z − φ_y(adj X)) where adj is the adjugate and φ_y(M) is a 4x4 matrix built from M and the 3x3 matrix Q(y) with diagonal entries y_i²+y_{i+1}² (indices mod 3) and off-diagonal entries −y_i y_j, is homogeneous of degree 20, and, third, its total degree is exactly 20. Fourth, it takes the value 1 at the base point where X and Z are both the identity matrix and y=0. Fifth, for every point x, the univariate polynomial obtained by substituting t·(base point) − x for the coordinates has only real roots, so any complex root has zero imaginary part; this is the hyperbolicity of the polynomial with respect to the base point. Sixth, for every positive integer N and every real-linear map L from the ambient space to the real symmetric N×N matrices, the cone of points x for which all complex roots t of that line polynomial are real and nonnegative is not equal to the set of x for which L(x) is positive semidefinite; that is, the hyperbolicity cone has no spectrahedral representation of any size.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/HyperbolicCones.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/HyperbolicCones.lean; bytes 2177..2587
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_HyperbolicCones

namespace OAI

noncomputable section

open scoped Matrix.Norms.L2Operator

universe u

namespace Paper256

theorem main_result :
    Module.finrank ℝ Ambient = 23 ∧
    polynomial.IsHomogeneous 20 ∧
    polynomial.totalDegree = 20 ∧
    MvPolynomial.eval (coordinates basePoint) polynomial = 1 ∧
    (∀ (x : Ambient) (z : ℂ), (linePolynomial x).aeval z = 0 → z.im = 0) ∧
    ∀ (N : ℕ) (_hN : 0 < N) (L : Ambient →ₗ[ℝ] Sym N),
      cone ≠ {x | (L x : Mat N ℝ).PosSemidef} := by
  sorry

end Paper256
end
end OAI
