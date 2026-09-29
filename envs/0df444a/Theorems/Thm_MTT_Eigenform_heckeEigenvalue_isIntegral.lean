-- Prove2me | Theorems.Thm_MTT_Eigenform_heckeEigenvalue_isIntegral
-- name    : MTT.Eigenform.heckeEigenvalue_isIntegral
-- status  : Proved
-- author  : @davidloeffler
-- created : 2026-09-18T21:13:51.022424+00:00
-- url     : https://prove2.me/theorems/b602e93d-e30a-4a10-989b-4f770faf14f9
-- title:
--   Prime Hecke eigenvalues are algebraic integers
-- statement:
--   For a normalized algebraic Hecke eigenform f of positive level and weight at least two, the eigenvalue a_ell(f) is integral over Z for every prime ell.
--
--   The intended reduction uses the nonzero finitely generated period-evaluation lattice stable under multiplication by a_ell(f), and the standard finite-module criterion for integrality.
-- source:
--   Standard integrality criterion for an element preserving a nonzero faithful finite lattice, applied to the integral parabolic-cohomology lattice.

import Definitions.Def_MTT_Arithmetic
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

set_option autoImplicit false
noncomputable section

theorem MTT.Eigenform.heckeEigenvalue_isIntegral
    {N k : ℕ} (hN : 0 < N) (hk : 2 ≤ k)
    (ι : MTT.Qbar →+* ℂ) (f : MTT.Eigenform N k ι)
    (l : ℕ) (hl : l.Prime) :
    IsIntegral ℤ (f.coeff l) := by
  sorry
