-- Prove2me | Theorems.Thm_MTT_Cohomology_evaluation_faithful
-- name    : MTT.Cohomology.evaluation_faithful
-- status  : Proved
-- author  : @allychan327
-- created : 2026-09-06T16:49:20.233718+00:00
-- url     : https://prove2.me/theorems/d8288d98-3f41-45b3-86c4-c5bc698df897
-- title:
--   Integral evaluations on paths to infinity separate classes
-- statement:
--   Two compactly supported cohomology classes with the same integral coefficient evaluations on every path from the cusp at infinity to a rational cusp, in every degree from 0 to n, are equal. The coefficient module is homogeneous of degree n in two variables, so the listed evaluations exhaust the coefficients of the value at each such path; the cocycle relation then propagates the agreement to all pairs of cusps. This holds over an arbitrary commutative coefficient ring.
-- source:
--   Manin, Parabolic points and zeta functions of modular curves, Izv. Akad. Nauk SSSR 36 (1972), §1.3-1.4; Mazur-Tate-Teitelbaum, Invent. Math. 84 (1986), §4

import Definitions.Def_MTT_Cohomology
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MTT.Cohomology

theorem MTT.Cohomology.evaluation_faithful
    {N n : ℕ} {R : Type*} [CommRing R] (φ ψ : Hc N n R)
    (h : ∀ j r, j ≤ n → evaluation j r φ = evaluation j r ψ) :
    φ = ψ := by sorry
