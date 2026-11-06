-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_sixth_power_eq_implies_same_prime_ideal
-- name    : OAI.ActualEisensteinCubic.sixth_power_eq_implies_same_prime_ideal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:22:00.190629+00:00
-- url     : https://prove2.me/theorems/6d2a680a-d59a-4831-ba50-4db53145edeb
-- title:
--   Actual Eisenstein Cubic: sixth power eq implies same prime ideal
-- statement:
--   The Actual Eisenstein Cubic construction uses the sixth power eq implies same prime ideal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/QuadraticTrace.lean#L94-L107
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/QuadraticTrace.lean#L94-L107

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_LatticeCount
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_QuadraticTrace
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
open OAI.ActualEisensteinCubic

theorem OAI.ActualEisensteinCubic.sixth_power_eq_implies_same_prime_ideal
    (p q : O)
    (hp : (Ideal.span {p} : Ideal O).IsMaximal)
    (hq : (Ideal.span {q} : Ideal O).IsMaximal)
    (h : p ^ 6 = q ^ 6) :
    (Ideal.span {p} : Ideal O) = Ideal.span {q} := by sorry
