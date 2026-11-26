-- Prove2me | Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_nonnegative_iff
-- name    : FourierJacobi.Valuations.localFieldValuation_nonnegative_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:49:09.976641+00:00
-- url     : https://prove2.me/theorems/c9b7a6a5-2866-4848-b800-4d4cce6e9b39
-- title:
--   Valuations: local Field Valuation nonnegative iff
-- statement:
--   The nonnegative valuation locus is the actual valuation ring.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/LocalField.lean#L115-L122
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/LocalField.lean#L115-L122

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

theorem FourierJacobi.Valuations.localFieldValuation_nonnegative_iff (x : K) :
    0 ≤ localFieldValuation K x ↔ x ∈ (ValuativeRel.valuation K).integer := by sorry
