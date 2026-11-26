-- Prove2me | Theorems.Thm_FourierJacobi_Valuations_central_majorant
-- name    : FourierJacobi.Valuations.central_majorant
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:20:32.227585+00:00
-- url     : https://prove2.me/theorems/16b11491-eb59-4308-9018-b010d97ef7a0
-- title:
--   Valuations: central majorant
-- statement:
--   The elementary inequality underlying the fixed-central-coordinate majorant.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/Cartan.lean#L132-L134
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/Cartan.lean#L132-L134

import Mathlib.Data.Int.Order.Basic
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.NormNum
import Mathlib.Algebra.Ring.Parity
import Definitions.Def_FourierJacobi_Valuations_Cartan
set_option autoImplicit false
open FourierJacobi
open FourierJacobi.Valuations

theorem FourierJacobi.Valuations.central_majorant (u v : ℤ) :
    2 * (u + v - max u v - max u (2 * v)) ≤ -max u v := by sorry
