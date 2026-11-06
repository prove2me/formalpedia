-- Prove2me | Theorems.Thm_OAI_PoissonFirstLocal_exponent_table
-- name    : OAI.PoissonFirstLocal.exponent_table
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:19:40.795706+00:00
-- url     : https://prove2.me/theorems/55f91e98-cf82-46dc-80a2-4c2cca7974fd
-- title:
--   Poisson First Local: exponent table
-- statement:
--   The Poisson First Local construction uses the exponent table property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L190-L193
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/GaussSum/FiniteFourier.lean#L190-L193

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinIdeals
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
import Definitions.Def_OAI_NumberTheory_DirichletL_GaussSum_FiniteFourier
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
open OAI.PoissonFirstLocal
open scoped Classical

theorem OAI.PoissonFirstLocal.exponent_table (parityBit ε₁ ε₂ : Bool) :
    totalExp₁ parityBit ε₁ ε₂ % 6 = (if retained parityBit ε₁ ε₂ then 4 else 0) ∧
    totalExp₂ parityBit ε₁ ε₂ % 6 = (if retained parityBit ε₁ ε₂ then 4 else 0) := by sorry
