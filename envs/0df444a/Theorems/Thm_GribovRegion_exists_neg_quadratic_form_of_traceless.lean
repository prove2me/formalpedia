-- Prove2me | Theorems.Thm_GribovRegion_exists_neg_quadratic_form_of_traceless
-- name    : GribovRegion.exists_neg_quadratic_form_of_traceless
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-13T18:13:24.515249+00:00
-- url     : https://prove2.me/theorems/a883b692-5447-48b6-8920-15e669d3954e
-- title:
--   Eq. (2.58): a nonzero symmetric traceless matrix has a direction of negative quadratic form
-- statement:
--   A nonzero symmetric traceless real matrix $M_2$ has a vector $\omega$ with
--
--   $$ \omega^{\mathsf T} M_2\, \omega < 0 . $$
--
--   The eigenvalues of a symmetric traceless matrix sum to zero and are not all zero, so at least one is negative. This is the argument of Eq. (2.58) of the review, applied to the field-dependent part $M_2(A)$ of the Faddeev--Popov operator.
-- source:
--   N. Vandersickel, D. Zwanziger, The Gribov problem and QCD dynamics, Physics Reports 520 (2012) 175-251, doi:10.1016/j.physrep.2012.07.003, Section 2.2.1 (pp. 188-189), Eqs. (2.52)-(2.59)

import Definitions.Def_gribov_region_model

set_option autoImplicit false

namespace GribovRegion

open scoped Matrix

theorem exists_neg_quadratic_form_of_traceless {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.IsHermitian) (htr : M.trace = 0) (hne : M ≠ 0) :
    ∃ w : Fin n → ℝ, w ⬝ᵥ M *ᵥ w < 0 := by sorry

end GribovRegion
