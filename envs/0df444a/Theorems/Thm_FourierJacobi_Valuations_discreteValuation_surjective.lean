-- Prove2me | Theorems.Thm_FourierJacobi_Valuations_discreteValuation_surjective
-- name    : FourierJacobi.Valuations.discreteValuation_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T11:18:40.32249+00:00
-- url     : https://prove2.me/theorems/bceaefce-889a-4201-84cc-9cd4d746b24b
-- title:
--   Valuations: discrete Valuation surjective
-- statement:
--   The Valuations construction uses the discrete Valuation surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/LocalField.lean#L81-L83
-- source:
--   https://github.com/abhisaha-git/fourier-jacobi-core-evaluation/blob/fb2b788d6271dd6228044b2c4e9e47c891a16762/FourierJacobi/Valuations/LocalField.lean#L81-L83

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

theorem FourierJacobi.Valuations.discreteValuation_surjective : Function.Surjective (discreteValuation K) := by sorry
