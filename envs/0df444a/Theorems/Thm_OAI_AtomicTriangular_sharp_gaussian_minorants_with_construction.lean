-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_sharp_gaussian_minorants_with_construction
-- name    : OAI.AtomicTriangular.sharp_gaussian_minorants_with_construction
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:21.924989+00:00
-- url     : https://prove2.me/theorems/5bf8dbc1-8cbe-4c65-b812-cd4596f18862
-- statement:
--   The theorem states that for every real α > 0 there is a real-valued radial Schwartz function f on ℝ² such that f(x) ≤ exp(−πα‖x‖²) everywhere, its Fourier transform is real and nonnegative everywhere, f agrees with this Gaussian at every nonzero point of the triangular lattice A = {b⁻¹ᐟ²(j+k/2,kb): j,k ∈ ℤ}, where b = √3/2, and its Fourier transform vanishes at every nonzero point of the dual lattice {w: ⟨a,w⟩ ∈ ℤ for all a ∈ A}. Radial means that f depends only on ‖x‖, and Schwartz means smooth with rapidly decreasing derivatives. If α ≥ 1, the same f additionally has the specified atomic construction: the fixed 20-by-20 interpolation matrix R has both I−R and I+R invertible, and the prescribed matrices U₊ and U₋ solve their stated interpolation equations. There are two coefficient families, indexed by sides 0 and 1, each with 11 finite coefficient pairs and absolutely summable tail pairs. Their finite coefficients are the prescribed matrix formulas evaluated at z = 1/[π(α/b−17/50)] and the parameter vector (z,1,ze^(−2/z),e^(−2/z),ze^(−3/z),e^(−3/z),ze^(−6/z),e^(−6/z)), with corrections to the final 20 finite coefficients whose sum of absolute values is less than 10⁻⁵ on each side. Each tail has total absolute coefficient sum less than 3×10⁻⁹. The input functions use the squared sine product P(s) = ∏ᵣ[2 sin(π(s−r)/36)]² over r ∈ {0,1,3,4,7,9,12,13,16,19,21,25,27,28,31}, its divided-difference interpolation functions at positive integers in these residue classes, and the prescribed finite trigonometric basis. The tail and finite parts have respective factors exp(−π(17/50)b‖x‖²) and exp(−π(27/50)b‖x‖²); the coefficients of P in the two tail parts are −3/500 and 3/500. Finally, f is the sum of the first input and the Fourier transform of the second, divided by Q(1)ze^(1/z), where Q(1) = P″(1)/2.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/TriangularGaussian.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/TriangularGaussian.lean; bytes 9208..9627
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_TriangularGaussian

namespace OAI

noncomputable section

open scoped BigOperators FourierTransform

namespace AtomicTriangular

open Construction

theorem sharp_gaussian_minorants_with_construction (α : ℝ) (hα : 0 < α) :
    ∃ f : SchwartzMap Plane ℝ,
      Radial f ∧ (∀ x, f x ≤ gaussian α x) ∧
      (∀ w, (realFourier f w).im = 0 ∧ 0 ≤ (realFourier f w).re) ∧
      (∀ a ∈ A, a ≠ 0 → f a = gaussian α a) ∧
      (∀ w ∈ dualA, w ≠ 0 → realFourier f w = 0) ∧
      (1 ≤ α → AtomicConstruction α f) := by
  sorry

end AtomicTriangular
end
end OAI
