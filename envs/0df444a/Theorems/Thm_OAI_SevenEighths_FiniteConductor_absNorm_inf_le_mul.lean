-- Prove2me | Theorems.Thm_OAI_SevenEighths_FiniteConductor_absNorm_inf_le_mul
-- name    : OAI.SevenEighths.FiniteConductor.absNorm_inf_le_mul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:13:44.871654+00:00
-- url     : https://prove2.me/theorems/0bd66502-afc2-4f0c-b5ea-7df8dba42dcb
-- title:
--   Finite Conductor: abs Norm inf le mul
-- statement:
--   The Finite Conductor construction uses the abs Norm inf le mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ConductorBounds.lean#L139-L142
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/ConductorBounds.lean#L139-L142

import Definitions.Def_OAI_NumberTheory_DirichletL_FiniteConductor
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Definitions.Def_OAI_NumberTheory_DirichletL_ConductorBounds
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.FiniteConductor
open SevenEighths.FiniteFourier
open scoped Classical
noncomputable section
variable {A : Type*} [CommRing A] [hDedekind : IsDedekindDomain A] [hInfinite : Infinite A]
include hDedekind hInfinite

theorem OAI.SevenEighths.FiniteConductor.absNorm_inf_le_mul (I J : Ideal A) [Finite (A ⧸ I)] [Finite (A ⧸ J)] :
    (I ⊓ J).cardQuot ≤ I.cardQuot * J.cardQuot := by sorry
