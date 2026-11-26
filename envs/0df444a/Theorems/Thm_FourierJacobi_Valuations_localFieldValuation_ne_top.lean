-- Prove2me | Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_ne_top
-- name    : FourierJacobi.Valuations.localFieldValuation_ne_top
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:46:20.21269+00:00
-- url     : https://prove2.me/theorems/0ef21d01-bff5-5240-acc1-25aa789243b7
-- title:
--   Valuations: local Field Valuation ne top
-- statement:
--   Finite additive valuations are obtained exactly at nonzero field elements.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/LocalField.lean#L98-L100
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/LocalField.lean#L98-L100

import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Lean.Elab.Tactic.Omega
import Definitions.Def_FourierJacobi_Valuations_LocalField
set_option autoImplicit false
noncomputable section
open scoped WithZero
open FourierJacobi FourierJacobi.Valuations
variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

theorem FourierJacobi.Valuations.localFieldValuation_ne_top (x : K) :
    localFieldValuation K x ≠ ⊤ ↔ x ≠ 0 := by sorry
