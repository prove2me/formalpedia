-- Prove2me | Theorems.Thm_MTT_Cohomology_finite_over_noetherian
-- name    : MTT.Cohomology.finite_over_noetherian
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-06T17:15:12.897726+00:00
-- url     : https://prove2.me/theorems/02dc9e11-996b-410a-b936-3f7bdac06dd4
-- title:
--   Finite generation over an arbitrary Noetherian coefficient ring
-- statement:
--   For positive level N and any Noetherian commutative coefficient ring R, the compactly supported group cohomology of Gamma_1(N) with degree n binary form coefficients is a finitely generated R-module. This extends the integral finite generation statement from Z to every Noetherian ring, and in particular gives finite dimensionality over a field, which is the form needed when comparing complex and algebraic Hecke eigenspaces.
-- source:
--   Manin, Parabolic points and zeta functions of modular curves, Izv. Akad. Nauk SSSR 36 (1972), §1; Mazur-Tate-Teitelbaum, Invent. Math. 84 (1986), §4

import Definitions.Def_MTT_Cohomology
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MTT.Cohomology

theorem MTT.Cohomology.finite_over_noetherian
    {N n : ℕ} (hN : 0 < N) (R : Type*) [CommRing R] [IsNoetherianRing R] :
    Module.Finite R (Hc N n R) := by sorry
