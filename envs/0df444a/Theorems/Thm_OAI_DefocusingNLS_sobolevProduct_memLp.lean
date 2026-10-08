-- Prove2me | Theorems.Thm_OAI_DefocusingNLS_sobolevProduct_memLp
-- name    : OAI.DefocusingNLS.sobolevProduct_memLp
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:32:07.084502+00:00
-- url     : https://prove2.me/theorems/206beb75-9bdd-4e08-9570-892883074bce
-- statement:
--   The theorem states that, for every real k > 6 and every pair f, g of elements of the square-summable complex sequence space ℓ² indexed by the frequency lattice (the integer span of the standard basis of twelve-dimensional Euclidean space, so ℤ¹²), the sequence n ↦ (1+‖n‖²)^(k/2) · c(n) is itself square-summable, where ‖n‖ is the Euclidean norm of n. Here c(n) is the convolution of the Sobolev-normalized coefficients of f and g: the sum over lattice points m of a_f(m)·a_g(n−m), with a_h(m) = (1+‖m‖²)^(−k/2) h(m). Thus the product coefficients, weighted by (1+‖n‖²)^(k/2), lie in ℓ², which expresses closure of the order-k Sobolev space on the twelve-dimensional torus under pointwise products at the level of Fourier coefficients. The sum defining c(n) is the formal tsum, with no separate hypothesis on its summability.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/DefocusingNLS.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/DefocusingNLS.lean; bytes 3920..4109
-- Kind: theorem; definition proof obligation extracted; recipe defocusing_nls_sobolev_product recorded in manifest.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_DefocusingNLS

namespace OAI

noncomputable section

open Set Filter Topology MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal ComplexConjugate ContDiff

attribute [local instance 2000] instPolynormableSpace
  TopologicalSpace.PseudoMetrizableSpace.regularSpace

namespace DefocusingNLS

theorem sobolevProduct_memLp (k : ℝ) (hk : 6 < k) (f g : FourierL2) :
    Memℓp (fun n : frequencyLattice =>
      (sobolevProductWeight k n : ℂ) * sobolevProductCoefficient k f g n)
      (2 : ℝ≥0∞) := by
  sorry

end DefocusingNLS
end
end OAI
