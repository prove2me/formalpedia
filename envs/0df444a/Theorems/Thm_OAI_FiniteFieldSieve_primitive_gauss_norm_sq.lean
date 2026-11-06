-- Prove2me | Theorems.Thm_OAI_FiniteFieldSieve_primitive_gauss_norm_sq
-- name    : OAI.FiniteFieldSieve.primitive_gauss_norm_sq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:14:24.793425+00:00
-- url     : https://prove2.me/theorems/27da0a88-30ee-4ea5-a449-cde23dad86ad
-- title:
--   Finite Field Sieve: primitive gauss norm sq
-- statement:
--   The Finite Field Sieve construction uses the primitive gauss norm sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LogProfiles.lean#L285-L296
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LogProfiles.lean#L285-L296

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.FiniteFieldSieve
variable {F : Type*} [Field F] [Fintype F]

theorem OAI.FiniteFieldSieve.primitive_gauss_norm_sq (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (hψ : ψ.IsPrimitive) :
    ‖gaussSum χ ψ‖ ^ 2 = (Fintype.card F : ℝ) := by sorry
