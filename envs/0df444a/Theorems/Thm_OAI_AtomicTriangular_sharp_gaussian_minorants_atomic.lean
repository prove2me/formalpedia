-- Prove2me | Theorems.Thm_OAI_AtomicTriangular_sharp_gaussian_minorants_atomic
-- name    : OAI.AtomicTriangular.sharp_gaussian_minorants_atomic
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:21.72354+00:00
-- url     : https://prove2.me/theorems/a2db0b83-7918-4b0f-81f0-23c40da2f043
-- statement:
--   The theorem states that, for every real α>0, there exists a real-valued radial Schwartz function f on ℝ² such that f(x)≤exp(−πα‖x‖²) everywhere, its Fourier transform is real and nonnegative everywhere, f agrees with this Gaussian at every nonzero point of the triangular lattice A={b⁻¹ᐟ²(j+k/2,kb):j,k∈ℤ}, where b=√3/2, and its Fourier transform vanishes at every nonzero point of the dual lattice A*={w:⟨a,w⟩∈ℤ for every a∈A}. Radial means that f depends only on ‖x‖, and Schwartz means smooth with all derivatives rapidly decreasing. For α≥1, f additionally has the specified atomic construction: writing r=b‖x‖², h=17/50, H=27/50, z=1/[π(α/b−h)], it is a normalized sum g₀+ĝ₁, where each gᵢ combines an exp(−πhr)-weighted sine-product expansion with an exp(−πHr)-weighted finite expansion. The sine product is P(s)=∏ₐ[2sin(π(s−a)/36)]² over a∈{0,1,3,4,7,9,12,13,16,19,21,25,27,28,31}; the infinite atoms are its first and second divided differences at positive integers in these residue classes, excluding {1,3,4,7,9,12,13,16,19,21}, and the finite atoms come from removing one squared sine factor, with the associated sine-cosine factors, at the first eleven listed residues. The two coefficients of P are respectively −3/500 and 3/500, and each finite expansion begins with coefficients 11/25 and 0. Its remaining twenty coefficients follow the defined finite matrix formulas in the parameter vector (z,1,ze^(−2/z),e^(−2/z),ze^(−3/z),e^(−3/z),ze^(−6/z),e^(−6/z)), with an additive correction whose sum of absolute values is less than 10⁻⁵ on each side. Each side’s infinite coefficient pair sequence is absolutely summable with total absolute sum less than 3×10⁻⁹. The construction also asserts invertibility of its two fixed twenty-dimensional matrices I−R and I+R and the exact defining linear-system identities for their solutions. The normalization is Q(1)ze^(1/z), where Q(n)=P″(n)/2.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/AtomicGaussian.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/AtomicGaussian.lean; bytes 8390..8814
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_AtomicGaussian

namespace OAI

noncomputable section

open scoped BigOperators FourierTransform SchwartzMap

open Complex Polynomial

namespace AtomicTriangular

theorem sharp_gaussian_minorants_atomic (α : ℝ) (hα : 0 < α) :
    ∃ f : SchwartzMap Plane ℝ,
      Radial f ∧ (∀ x, f x ≤ gaussian α x) ∧
      (∀ w, (realFourier f w).im = 0 ∧ 0 ≤ (realFourier f w).re) ∧
      (∀ a ∈ A, a ≠ 0 → f a = gaussian α a) ∧
      (∀ w ∈ dualA, w ≠ 0 → realFourier f w = 0) ∧
      (1 ≤ α → Construction.HasAtomicConstruction α f) := by
  sorry

end AtomicTriangular
end
end OAI
