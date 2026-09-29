-- Prove2me | Theorems.Thm_HorizontalPadicL_eigenform_residualGaloisRepresentation_exists_v2
-- name    : HorizontalPadicL.eigenform_residualGaloisRepresentation_exists_v2
-- status  : Open
-- author  : @davidloeffler
-- created : 2026-09-20T11:20:22.454776+00:00
-- url     : https://prove2.me/theorems/813fe5d1-f931-4a2c-afc7-ad2fac39d094
-- title:
--   The residual Galois representation of a normalized eigenform
-- statement:
--   **This is a formalization of a standard textbook result, so should be low-priority**
--
--   Let $N>0$, let $k\geq2$, let $p$ be prime, and let $f$ be a normalized
--   algebraic cuspidal Hecke eigenform of level $N$, weight $k$, and nebentype
--   $\varepsilon_f$. For every embedding
--   $\iota_p:\overline{\mathbf Q}\hookrightarrow\mathbf C_p$, there exists a
--   finite Galois extension $L/\mathbf Q$ and a faithful residual representation
--   $$
--   \bar\rho_{f,\iota_p}:\operatorname{Gal}(L/\mathbf Q)
--   \longrightarrow M_2(k_{f,\iota_p})
--   $$
--   over the canonical finite coefficient residue field. It is unramified outside
--   $Np$, and for every prime $\ell\nmid Np$ its arithmetic Frobenius satisfies
--   $$
--   \operatorname{tr}\bar\rho_{f,\iota_p}(\operatorname{Frob}_\ell)
--   =\overline{a_\ell(f)},\qquad
--   \det\bar\rho_{f,\iota_p}(\operatorname{Frob}_\ell)
--   =\overline{\varepsilon_f(\ell)\ell^{k-1}}.
--   $$
--
--   The representation is written on the finite Galois group of its kernel field,
--   which is equivalent to the usual finite-image representation of the absolute
--   Galois group.
-- source:
--   Deligne's construction of Galois representations attached to normalized eigenforms; as used in Kriz--Nordentoft, Horizontal p-adic L-functions, arXiv:2310.20678v3, Section 4, equation (4.2).

import Definitions.Def_KN_EigenformResidualGaloisRepresentationV2

set_option autoImplicit false
noncomputable section

namespace HorizontalPadicL

/-- **This is a formalization of a standard textbook result, so should be
low-priority.**

Deligne's residual Galois representation attached to a normalized
eigenform and a chosen `p`-adic embedding.  Its coefficient field is
`f.coefficientField`, its prime is the canonically defined
`f.coefficientPrime ιp`, and its target is the resulting finite residue field
`EigenformResidueField f ιp`; none of these are auxiliary choices in
the existence statement. -/
theorem eigenform_residualGaloisRepresentation_exists_v2
    {N k p : ℕ} [Fact p.Prime]
    (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (ιp : MTT.Qbar →+* ℂ_[p]) :
    Nonempty (EigenformResidualGaloisRepresentationData hN hk f ιp) := by sorry

end HorizontalPadicL
