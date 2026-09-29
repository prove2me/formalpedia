-- Prove2me | Theorems.Thm_HorizontalPadicL_seededHorizontalPadicLFunction_assemble_v4
-- name    : HorizontalPadicL.seededHorizontalPadicLFunction_assemble_v4
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-25T14:57:32.545857+00:00
-- url     : https://prove2.me/theorems/fb490c4e-b63a-4812-9aad-c4b8f7ee761a
-- title:
--   Package a faithful theta measure as a clean seeded horizontal p-adic L-function
-- statement:
--   A normalized theta measure with faithful character realization, interpolation, and nonzero trivial value packages with the original positive-density prime system to give a seeded horizontal p-adic L-function on the clean replacement definition spine.
--
--   This is the clean-spine replacement used to remove deprecated definition bundles from the live graph.
-- source:
--   Kriz--Nordentoft, Horizontal p-adic L-functions, https://arxiv.org/pdf/2310.20678, Corollary 3.6, Definition 5.3, Corollary 5.4, Theorem 5.9, Corollary 5.10 and Corollary 5.17.

import Definitions.Def_KN_SeededHorizontalPadicLFunctionV3B
import Definitions.Def_KN_SeededThetaConstructionV2B
import Definitions.Def_KN_InverseSeedConventionV2

set_option autoImplicit false
noncomputable section

namespace HorizontalPadicL

/-- Package a faithful normalized theta measure together with the original
positive-density prime system. -/
theorem seededHorizontalPadicLFunction_assemble_v4
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (hnew : IsNewEigenform f)
    (η : DirichletCharacterWithLevel) (ιp : MTT.Qbar →+* ℂ_[p])
    (L : SeededHorizontalPrimeSystemV3 p ιp f η B)
    (μ : SeededNormalizedThetaMeasureV3 L.toConstructionData)
    (hcharacters : μ.characters.HasExpectedProperties)
    (hinterp : μ.InterpolatesSeededCriticalValues)
    (htrivial : μ.measure.eval
      (trivialHorizontalCharacterV2 p L.toConstructionData.exponent) ≠ 0) :
    ∃ ν : SeededHorizontalPadicLFunctionV4 (B := B) p ιp f η,
      ν.primes = L ∧ ν.InterpolatesSeededCriticalValuesV4 ∧
      ν.measure.eval (trivialHorizontalCharacterV2 p ν.primes.exponent) ≠ 0 := by
  sorry

end HorizontalPadicL
