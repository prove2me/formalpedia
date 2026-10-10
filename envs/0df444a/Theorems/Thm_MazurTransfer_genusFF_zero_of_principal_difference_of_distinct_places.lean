-- Prove2me | Theorems.Thm_MazurTransfer_genusFF_zero_of_principal_difference_of_distinct_places
-- name    : MazurTransfer.genusFF_zero_of_principal_difference_of_distinct_places
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-09T21:22:00.226563+00:00
-- url     : https://prove2.me/theorems/eb2b3d28-896d-4965-9e2a-ee6e90db9221
-- title:
--   A principal difference of distinct places with a rational pole forces genus zero over a perfect field
-- statement:
--   Let F/K be a one-variable function field over a perfect field, with the full constant field equal to K and the finite-type curve hypotheses stated formally. If distinct places P and Q satisfy degree(Q)=1 and P−Q is principal, then the function-field genus is zero: \[ [P-Q]=0,\quad P\ne Q,\quad \deg Q=1 \quad\Longrightarrow\quad g(F/K)=0. \] Thus positive genus prevents two distinct rational places from having the same degree-zero divisor class. The proof uses Weil-canonical Riemann–Roch and does not assume an algebraically closed base field or a supplied canonical differential.
-- source:
--   Vas and contributors, MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0, https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c . Pole and independent-power argument from official Anthropic FLT at 6e837e75355538c7f80bab5b956861e86c4eacc2, Apache-2.0, https://github.com/anthropics/fermats-last-theorem/tree/6e837e75355538c7f80bab5b956861e86c4eacc2 . Separate checked perfect-field Weil-canonical adaptation; the original canonical-differential statement is unchanged.

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex
open AlgebraicCurve

theorem MazurTransfer.genusFF_zero_of_principal_difference_of_distinct_places.{u,v}
    {K : Type u} {F : Type v}
    [Field K] [PerfectField K] [Field F] [Algebra K F]
    [IsCurveOver K F] [Algebra.EssFiniteType K F]
    (hC : ConstantsAreBase K F) {P Q : AlgebraicCurve.Place K F}
    (hPQ : P ≠ Q) (hQ : Q.deg = 1)
    (h : Divisor.IsPrincipal (Finsupp.single P 1 - Finsupp.single Q 1)) :
    genusFF K F = 0 := by sorry
