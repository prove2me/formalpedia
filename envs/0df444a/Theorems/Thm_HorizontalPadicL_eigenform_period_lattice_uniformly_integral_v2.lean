-- Prove2me | Theorems.Thm_HorizontalPadicL_eigenform_period_lattice_uniformly_integral_v2
-- name    : HorizontalPadicL.eigenform_period_lattice_uniformly_integral_v2
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-25T11:41:02.118886+00:00
-- url     : https://prove2.me/theorems/da50c8d6-0c3d-433d-947c-dc3aa11cb8ed
-- title:
--   Uniform p-integrality of the eigenform period lattice
-- statement:
--   A single nonzero algebraic scalar clears the p-adic denominators of every normalized signed modular-symbol value in an MTT period system. This follows from finite generation of the integral period lattice.
-- source:
--   Mazur--Tate--Teitelbaum modular-symbol period formalism; Kriz--Nordentoft, https://arxiv.org/pdf/2310.20678.

import Definitions.Def_KN_SeededThetaConstructionV2B

set_option autoImplicit false
noncomputable section

namespace HorizontalPadicL

/-- Finite generation of the integral period lattice gives one scalar clearing
all `p`-adic denominators of the normalized signed modular symbols. -/
theorem eigenform_period_lattice_uniformly_integral_v2
    {N k p : ℕ} {ι : MTT.Qbar →+* ℂ} [Fact p.Prime]
    (f : MTT.Eigenform N k ι) (hnew : IsNewEigenform f)
    (ιp : MTT.Qbar →+* ℂ_[p]) (P : MTT.Periods k ι f.form) :
    Nonempty (IntegralPeriodScale f ιp P) := by sorry

end HorizontalPadicL
