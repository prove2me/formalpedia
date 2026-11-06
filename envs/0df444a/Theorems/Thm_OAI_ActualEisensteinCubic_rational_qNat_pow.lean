-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_rational_qNat_pow
-- name    : OAI.ActualEisensteinCubic.rational_qNat_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:47:59.285323+00:00
-- url     : https://prove2.me/theorems/6473705f-00f7-40ce-94fe-4b2cc0a651a0
-- title:
--   Actual Eisenstein Cubic: rational q Nat pow
-- statement:
--   The Actual Eisenstein Cubic construction uses the rational q Nat pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/GaussianMoments.lean#L118-L129
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/GaussianMoments.lean#L118-L129

import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_GaussianFiberMass
import Definitions.Def_OAI_NumberTheory_DirichletL_Poisson_GaussianMoments
set_option autoImplicit false
open OAI
noncomputable section
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open MeasureTheory Real
open scoped FourierTransform SchwartzMap
open Finset Complex
open scoped Classical
open scoped Classical
open Filter Real Asymptotics
open OAI.ActualEisensteinCubic
open ShortDraftLatticeCount

theorem OAI.ActualEisensteinCubic.rational_qNat_pow (r k : ℕ) (hr : r ≠ 0) :
    qNat ((r : O) ^ k) = (r ^ 2) ^ k := by sorry
