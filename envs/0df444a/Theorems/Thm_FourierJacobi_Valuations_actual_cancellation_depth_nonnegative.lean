-- Prove2me | Theorems.Thm_FourierJacobi_Valuations_actual_cancellation_depth_nonnegative
-- name    : FourierJacobi.Valuations.actual_cancellation_depth_nonnegative
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:28:21.032268+00:00
-- url     : https://prove2.me/theorems/44023d37-cd8a-5ed1-845b-288a3efb59a9
-- title:
--   Valuations: actual cancellation depth nonnegative
-- statement:
--   A finite cancellation depth is nonnegative on the collision locus.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/MatrixBridge.lean#L189-L200
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/MatrixBridge.lean#L189-L200

import Definitions.Def_FourierJacobi_Algebra_Matrices
import Definitions.Def_FourierJacobi_Valuations_Cartan
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Algebra.Order.AddGroupWithTop
import Mathlib.Tactic.LinearCombination
import Definitions.Def_FourierJacobi_Valuations_MatrixBridge
set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Valuations
open LocalMatrix
variable {K : Type*} [Field K]

theorem FourierJacobi.Valuations.actual_cancellation_depth_nonnegative (v : AddValuation K (WithTop ℤ))
    (x y z : K) (r j h c : ℤ)
    (hj : v x = j) (hh : v y = h) (hz : v z = (-r : ℤ))
    (heq : 2 * h = j - r) (hc : v (y ^ 2 / (x * z) - 1) = c) : 0 ≤ c := by sorry
