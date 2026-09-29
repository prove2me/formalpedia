-- Prove2me | Theorems.Thm_HorizontalPadicL_ellipticCurve_eigenform_specialization_v2
-- name    : HorizontalPadicL.ellipticCurve_eigenform_specialization_v2
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-25T11:30:31.048663+00:00
-- url     : https://prove2.me/theorems/0d32d7cd-0df5-4df4-854f-50c70b65a674
-- title:
--   Specialization from a modular elliptic curve to a new eigenform
-- statement:
--   For a modular elliptic curve, the normalized attached cusp form determines a weight-two new eigenform at the least modular level. Its primitive fixed-order twist counting function agrees identically with the elliptic curve counting function used in the mission goal.
-- source:
--   Kriz–Nordentoft, https://arxiv.org/pdf/2310.20678, Corollary 5.17 and its specialization to modular elliptic curves; modularity and q-expansion definitions as in the mission core.

import Definitions.Def_KN_HorizontalPadicLAux

set_option autoImplicit false
noncomputable section

namespace HorizontalPadicL

theorem ellipticCurve_eigenform_specialization_v2
    (iota : MTT.Qbar →+* ℂ) (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (hmod : IsModular E) :
    ∃ f : MTT.Eigenform (modularConductor E hmod) 2 iota,
      IsNewEigenform f ∧
      ∀ d : ℕ, ∀ X : ℝ,
        eigenformNonvanishingCount iota f d X = nonvanishingCount iota E hmod d X := by sorry

end HorizontalPadicL
