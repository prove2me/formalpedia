-- Prove2me | Theorems.Thm_GRH_smoothed_mobius_nine_tenths_nonprincipal
-- name    : GRH.smoothed_mobius_nine_tenths_nonprincipal
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T00:27:13.622296+00:00
-- url     : https://prove2.me/theorems/33820a85-16e3-4ef6-bcf0-d18f6d5f2b37
-- title:
--   A nine-tenths bound for the exponentially smoothed Möbius sum of a nonprincipal character
-- statement:
--   For every positive modulus $q$ and nonprincipal complex Dirichlet character $\chi$ modulo $q$, there is a constant $C_\chi>0$ such that for every real $D\ge1$,
--   $$
--   \left|\sum_{n\ge1}\mu(n)\chi(n)e^{-n/D}\right|\le C_\chi D^{9/10}.
--   $$
--   The constant may depend on the modulus and character. The exponent is fixed at $9/10$.
-- source:
--   Consequence of the Prove2Me fixed-strip zero-free result TowardsGRH_LW56e2_b83dbbd.dirichlet_zero_free_bound and polynomial reciprocal estimate GRH.reciprocal_nonprincipal_nine_tenths, using Mellin inversion and vertical contour displacement. See NIST Digital Library of Mathematical Functions, §2.5(i), https://dlmf.nist.gov/2.5.i.

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing

open OAI.ShortDraftMellin

theorem GRH.smoothed_mobius_nine_tenths_nonprincipal (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ D : ℝ, 1 ≤ D →
      ‖mobiusExpSum χ D⁻¹‖ ≤ C * D ^ (9 / 10 : ℝ) := by sorry
