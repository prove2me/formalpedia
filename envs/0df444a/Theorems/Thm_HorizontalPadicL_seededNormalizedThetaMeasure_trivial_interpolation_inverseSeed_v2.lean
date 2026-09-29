-- Prove2me | Theorems.Thm_HorizontalPadicL_seededNormalizedThetaMeasure_trivial_interpolation_inverseSeed_v2
-- name    : HorizontalPadicL.seededNormalizedThetaMeasure_trivial_interpolation_inverseSeed_v2
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-25T14:50:27.307521+00:00
-- url     : https://prove2.me/theorems/e954f63e-c077-4f71-889f-922003c7633d
-- title:
--   Seeded interpolation at the trivial horizontal character (inverse-seed convention)
-- statement:
--   If the faithful realization sends the trivial horizontal character to the trivial Dirichlet character, the general seeded interpolation property specializes to the original primitive seed character.
--
--   This replacement uses the inverse-seed convention matching MTT criticalLValue: the orderly-prime expression and Euler augmentation are eta(l)*a_l - eta(l)^2 - epsilon(l). The critical values and seed hypotheses themselves retain the character eta. It supersedes `HorizontalPadicL.seededNormalizedThetaMeasure_trivial_interpolation`.
-- source:
--   Formal specialization of the seeded interpolation definition; Kriz--Nordentoft, Corollary 5.4.

import Definitions.Def_KN_SeededFiniteThetaCriticalZeroSetV2
import Definitions.Def_KN_InverseSeedConventionV2

set_option autoImplicit false
noncomputable section

namespace HorizontalPadicL

/-- The general seeded interpolation property specializes at the trivial
horizontal character to the original primitive seed character. -/
theorem seededNormalizedThetaMeasure_trivial_interpolation_inverseSeed_v2
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (hηprim : η.2.IsPrimitive)
    (characters : SeededHorizontalCharacterRealizationV3 L)
    (hcharacters : characters.HasExpectedProperties)
    (μ : SeededNormalizedThetaMeasureV3 L)
    (hμcharacters : μ.characters = characters)
    (hinterp : μ.InterpolatesSeededCriticalValues) :
    μ.measure.eval (trivialHorizontalCharacterV2 p L.exponent) ≠ 0 ↔
      @MTT.criticalLValue ι f.form
        η.1.1 ⟨Nat.ne_of_gt η.1.2⟩ η.2 (k / 2 - 1) ≠ 0 := by
  sorry

end HorizontalPadicL
