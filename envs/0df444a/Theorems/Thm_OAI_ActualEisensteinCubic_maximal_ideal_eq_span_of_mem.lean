-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_maximal_ideal_eq_span_of_mem
-- name    : OAI.ActualEisensteinCubic.maximal_ideal_eq_span_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:48:26.304875+00:00
-- url     : https://prove2.me/theorems/cdeab7bb-573c-4229-9703-13d8a79ab2f1
-- title:
--   Actual Eisenstein Cubic: maximal ideal eq span of mem
-- statement:
--   The Actual Eisenstein Cubic construction uses the maximal ideal eq span of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/GaussianMoments.lean#L196-L202
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Poisson/GaussianMoments.lean#L196-L202

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

theorem OAI.ActualEisensteinCubic.maximal_ideal_eq_span_of_mem
    (Q : Ideal O) (hQ : Q.IsMaximal) (a : O)
    (ha : (Ideal.span {a} : Ideal O).IsMaximal) (hamem : a ∈ Q) :
    Q = Ideal.span {a} := by sorry
