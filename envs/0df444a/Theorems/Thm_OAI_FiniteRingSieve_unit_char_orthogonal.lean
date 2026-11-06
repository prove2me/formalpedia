-- Prove2me | Theorems.Thm_OAI_FiniteRingSieve_unit_char_orthogonal
-- name    : OAI.FiniteRingSieve.unit_char_orthogonal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:14:14.589203+00:00
-- url     : https://prove2.me/theorems/8584f39e-6453-4b04-b258-80e73a8df6e2
-- title:
--   Finite Ring Sieve: unit char orthogonal
-- statement:
--   The Finite Ring Sieve construction uses the unit char orthogonal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LogProfiles.lean#L200-L211
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LogProfiles.lean#L200-L211

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.FiniteRingSieve
variable {R : Type*} [CommRing R] [Fintype R] [DecidableEq R]
attribute [local instance] OAI.FiniteRingSieve.logProfilesFintypeMulChar
attribute [local instance] logProfilesFintypeMulChar

theorem OAI.FiniteRingSieve.unit_char_orthogonal (u v : Rˣ) :
    (∑ χ : MulChar R ℂ, star (χ (u : R)) * χ (v : R)) =
      if u = v then (Fintype.card Rˣ : ℂ) else 0 := by sorry
