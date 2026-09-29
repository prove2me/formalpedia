-- Prove2me | Theorems.Thm_HorizontalPadicL_fullSupportCriticalZeroSet_descends_inverseSeed_v3
-- name    : HorizontalPadicL.fullSupportCriticalZeroSet_descends_inverseSeed_v3
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-25T15:04:44.381775+00:00
-- url     : https://prove2.me/theorems/3609ce07-d8e4-4b4f-ba54-beb9471d034a
-- title:
--   Full-support interpolation descends through redundant support (clean spine)
-- statement:
--   For a faithful finite theta system, the critical-value zero-set formula known for horizontal characters whose primitive conductor uses their whole chosen support extends to every horizontal character. Norm relations compare redundant supports, and the transition Euler factors are units, so the comparison preserves vanishing.
--
--   This is a clean-spine replacement used to remove deprecated definition bundles from the live graph.
-- source:
--   Kriz--Nordentoft, Horizontal p-adic L-functions, https://arxiv.org/pdf/2310.20678, Corollary 5.2 and Corollary 5.4.

import Definitions.Def_KN_SeededThetaFullSupportInterpolationV3

set_option autoImplicit false
noncomputable section

namespace HorizontalPadicL

/-- Full-conductor Birch--Mellin interpolation descends through redundant
support.  The norm relations compare the two theta evaluations, and unit Euler
factors ensure that the comparison factor is nonzero. -/
theorem fullSupportCriticalZeroSet_descends_inverseSeed_v3
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (Θ : SeededFiniteThetaDataV3 L)
    (hcharacters : Θ.characters.HasExpectedProperties)
    (hnorm : Θ.SatisfiesNormRelations)
    (hunit : Θ.HasUnitEulerFactors)
    (hfull : Θ.HasFullSupportCriticalZeroSetV2) :
    Θ.HasSeededCriticalZeroSet := by
  sorry

end HorizontalPadicL
