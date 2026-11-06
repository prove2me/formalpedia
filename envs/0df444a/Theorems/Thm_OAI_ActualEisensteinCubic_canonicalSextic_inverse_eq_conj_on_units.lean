-- Prove2me | Theorems.Thm_OAI_ActualEisensteinCubic_canonicalSextic_inverse_eq_conj_on_units
-- name    : OAI.ActualEisensteinCubic.canonicalSextic_inverse_eq_conj_on_units
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-06T05:13:33.217391+00:00
-- url     : https://prove2.me/theorems/4ebe47b0-db9a-49b7-9da4-5984a1ffff07
-- title:
--   Actual Eisenstein Cubic: canonical Sextic inverse eq conj on units
-- statement:
--   The Actual Eisenstein Cubic construction uses the canonical Sextic inverse eq conj on units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/LocalProductAssembly.lean#L24-L32
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/LocalProductAssembly.lean#L24-L32

import Definitions.Def_OAI_NumberTheory_DirichletL_Cusp_MatrixPhases
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_SexticNormalization
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_LocalProductAssembly
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
open ConcreteTraceCRT
open scoped ComplexConjugate

theorem OAI.ActualEisensteinCubic.canonicalSextic_inverse_eq_conj_on_units (P : Ideal O)
    [P.IsMaximal] (hgood : lambda ∉ P) (u : (O ⧸ P)ˣ) :
    (canonicalSextic P hgood (u : O ⧸ P))⁻¹ =
      star (canonicalSextic P hgood (u : O ⧸ P)) := by sorry
