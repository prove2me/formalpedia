-- Prove2me | Theorems.Thm_OAI_PlanarAnderson_anderson_spectrum_ae
-- name    : OAI.PlanarAnderson.anderson_spectrum_ae
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:03.975575+00:00
-- url     : https://prove2.me/theorems/f200242a-79f4-4088-bea2-fb00b9d95659
-- statement:
--   The theorem states that for every real h>0, for almost every disorder configuration v under disorderLaw(h), there exists a bounded complex-linear operator H on the Hilbert space ℓ²(ℤ², ℂ) of square-summable complex functions on the planar lattice ℤ×ℤ such that H is an Anderson operator for v, H is self-adjoint, and the spectrum of H in ℂ equals the real interval [-4-h, 4+h] (embedded in ℂ as the points with imaginary part 0). Here a configuration is a real-valued function v on lattice sites, and disorderLaw(h) is the infinite product measure over sites of the uniform distribution (Lebesgue measure conditioned on the interval) on [-h,h], so the potential values are independent. H is an Anderson operator for v when, for every u in ℓ² and every site x=(a,b), (Hu)(a,b) = u(a+1,b)+u(a-1,b)+u(a,b+1)+u(a,b-1)+v(a,b)u(a,b), the sum of the four nearest-neighbour values plus the local potential times u at x. The statement is recorded as an admitted theorem.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PlanarAndersonSpectrum.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/PlanarAndersonSpectrum.lean; bytes 701..923
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_PlanarAndersonSpectrum

namespace OAI

noncomputable section

open MeasureTheory

open scoped ENNReal

namespace PlanarAnderson

theorem anderson_spectrum_ae {h : ℝ} (hh : 0 < h) :
    ∀ᵐ v ∂disorderLaw h, ∃ H : Hilbert →L[ℂ] Hilbert,
      IsAndersonOperator v H ∧ IsSelfAdjoint H ∧ spectrum ℂ H = spectralInterval h := by
  sorry

end PlanarAnderson
end
end OAI
