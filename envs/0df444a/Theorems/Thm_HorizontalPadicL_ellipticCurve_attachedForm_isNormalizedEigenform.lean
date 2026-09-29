-- Prove2me | Theorems.Thm_HorizontalPadicL_ellipticCurve_attachedForm_isNormalizedEigenform
-- name    : HorizontalPadicL.ellipticCurve_attachedForm_isNormalizedEigenform
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-17T18:46:58.43997+00:00
-- url     : https://prove2.me/theorems/ed384a33-14c3-4820-90c0-420e322533f1
-- title:
--   The modular form attached to an elliptic curve is a normalized eigenform
-- statement:
--   For a modular elliptic curve over the rationals, the chosen least-level weight-two cusp form whose q-expansion equals the elliptic curve L-series satisfies the normalized eigenform coefficient relations: normalization, coprime multiplicativity, and the good- and bad-prime power recurrences.
-- source:
--   The Euler product for the Hasse–Weil L-function of an elliptic curve, together with the normalized eigenform coefficient criterion; see Diamond–Shurman, A First Course in Modular Forms, Proposition 5.8.5, and Kriz–Nordentoft, Corollary 5.17.

import Definitions.Def_KN_HorizontalPadicL
import Definitions.Def_FLTPrelim_Modularity

set_option autoImplicit false

namespace HorizontalPadicL

/-- The q-expansion attached to an elliptic curve satisfies the normalized Hecke-eigenform
coefficient relations.  Concretely, this consists of `a₁ = 1`, multiplicativity at
coprime indices, and the good- and bad-prime recurrences for prime powers. -/
theorem ellipticCurve_attachedForm_isNormalizedEigenform
    (E : WeierstrassCurve ℚ) [E.IsElliptic] (hmod : IsModular E) :
    CuspForm.IsNormalizedEigenform (modularFormAtConductor E hmod).form := by sorry

end HorizontalPadicL
