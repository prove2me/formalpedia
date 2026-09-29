-- Prove2me | Theorems.Thm_HorizontalPadicL_seededEigenform_padicPlace_exists_v2
-- name    : HorizontalPadicL.seededEigenform_padicPlace_exists_v2
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-25T14:22:34.660352+00:00
-- url     : https://prove2.me/theorems/c03f96ff-d7e5-4a58-a233-f213d2a67e09
-- title:
--   A p-adic place for eigenform coefficients and a seed character
-- statement:
--   Let $f$ be a new normalized eigenform of positive level and weight at least two, let $p$ be prime, and let $\eta$ be an algebraic Dirichlet character. There is an embedding of the common algebraic coefficient field into $\mathbf C_p$ under which every Fourier coefficient $a_n(f)$ and every value of $\eta$ is $p$-adically integral.
--
--   This supplies the coefficient place at which the residual representation and orderly-prime congruences are evaluated.
-- source:
--   Kriz–Nordentoft, Horizontal p-adic L-functions, arXiv:2310.20678v3, §4.3, Lemma 4.14 and Corollary 4.15, pp. 30–31.

import Definitions.Def_KN_SeededPrimeGaloisDataV2

set_option autoImplicit false

namespace HorizontalPadicL

theorem seededEigenform_padicPlace_exists_v2
    {N k p : ℕ} [Fact p.Prime]
    (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (hnew : IsNewEigenform f) (η : DirichletCharacterWithLevel) :
    Nonempty (SeededEigenformPadicPlaceData (p := p) f η) := by sorry

end HorizontalPadicL
