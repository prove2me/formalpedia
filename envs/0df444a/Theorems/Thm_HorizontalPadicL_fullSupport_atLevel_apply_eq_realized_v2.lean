-- Prove2me | Theorems.Thm_HorizontalPadicL_fullSupport_atLevel_apply_eq_realized_v2
-- name    : HorizontalPadicL.fullSupport_atLevel_apply_eq_realized_v2
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-25T14:29:34.429416+00:00
-- url     : https://prove2.me/theorems/516dbfa3-8137-4900-bc4d-fea61cccefd6
-- title:
--   Full support identifies the level character with its primitive realization
-- statement:
--   When the conductor of the primitive realization is the entire selected support modulus, the level character used in the horizontal quotient agrees with that primitive character on every unit. Integer representatives are used to avoid transports between equal ZMod levels.
-- source:
--   Kriz--Nordentoft, Horizontal p-adic L-functions, https://arxiv.org/pdf/2310.20678, Corollary 3.6 and Corollary 5.4; standard Dirichlet-character and modular-symbol identities.

import Definitions.Def_KN_SeededInverseThetaSystemV2

set_option autoImplicit false
noncomputable section

namespace HorizontalPadicL

/-- If a horizontal character uses its full conductor, then the full-level
character used in the quotient construction agrees, on units, with its
primitive realization.  The formulation on integer representatives avoids
dependent transports between equal `ZMod` levels. -/
theorem fullSupport_atLevel_apply_eq_realized_v2
    {N k p B : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    {ιp : MTT.Qbar →+* ℂ_[p]} {f : MTT.Eigenform N k ι}
    {η : DirichletCharacterWithLevel}
    {L : SeededHorizontalPrimeDataV3 p ιp f η B}
    (R : SeededHorizontalCharacterRealizationV3 L)
    (χ : HorizontalCharacter p L.exponent)
    (hfull : (R.realized χ).2.conductor = L.supportModulus χ.support)
    (u : (ZMod (L.supportModulus χ.support))ˣ) :
    R.atLevel χ u.val.val = (R.realized χ).2 u.val.val := by
  sorry

end HorizontalPadicL
