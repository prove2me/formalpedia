-- Prove2me | Theorems.Thm_FourierJacobi_Valuations_localFieldValuation_surjective
-- name    : FourierJacobi.Valuations.localFieldValuation_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:18:36.721257+00:00
-- url     : https://prove2.me/theorems/4453b5ac-933e-49f5-bb1a-1440341821f8
-- title:
--   Valuations: local Field Valuation surjective
-- statement:
--   The Valuations construction uses the local Field Valuation surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/LocalField.lean#L102-L112
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/LocalField.lean#L102-L112

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

theorem FourierJacobi.Valuations.localFieldValuation_surjective : Function.Surjective (localFieldValuation K) := by sorry
