-- Prove2me | Theorems.Thm_MTT_Cohomology_manin_coordinates
-- name    : MTT.Cohomology.manin_coordinates
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-06T17:15:06.2458+00:00
-- url     : https://prove2.me/theorems/691c3316-d875-4897-9923-5d4b4d2a0395
-- title:
--   Finite Manin coordinates embed compactly supported cohomology
-- statement:
--   For positive level N, the compactly supported group cohomology of the congruence subgroup Gamma_1(N) with degree n binary form coefficients admits an injective R-linear map into a finite free module, for every commutative coefficient ring R, with a rank not depending on R. The coordinates may be taken to be the coefficients of X^j Y^(n-j), for 0 <= j <= n, on the unimodular paths attached to a fixed set of representatives for the finitely many right cosets of Gamma_1(N) in SL(2,Z). Only the generation half of Manin's theory is used, not the presentation, so no relation among the coordinates is asserted.
-- source:
--   Manin, Parabolic points and zeta functions of modular curves, Izv. Akad. Nauk SSSR 36 (1972), §1; Mazur-Tate-Teitelbaum, Invent. Math. 84 (1986), §4

import Definitions.Def_MTT_Cohomology
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MTT.Cohomology

theorem MTT.Cohomology.manin_coordinates
    {N n : ℕ} (hN : 0 < N) (R : Type*) [CommRing R] :
    ∃ (m : ℕ) (T : Hc N n R →ₗ[R] (Fin m → R)), Function.Injective T := by sorry
