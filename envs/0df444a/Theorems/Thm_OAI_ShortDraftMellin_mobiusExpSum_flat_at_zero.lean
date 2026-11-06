-- Prove2me | Theorems.Thm_OAI_ShortDraftMellin_mobiusExpSum_flat_at_zero
-- name    : OAI.ShortDraftMellin.mobiusExpSum_flat_at_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:13:34.495829+00:00
-- url     : https://prove2.me/theorems/172cd2d2-5c99-46df-aca5-d2536ec5e3e8
-- title:
--   Short Draft Mellin: mobius Exp Sum flat at zero
-- statement:
--   The Short Draft Mellin construction uses the mobius Exp Sum flat at zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/ExponentialSmoothing.lean#L562-L583
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/ExponentialSmoothing.lean#L562-L583

import Definitions.Def_OAI_NumberTheory_DirichletL_Arithmetic_EisensteinCoordinates
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.ShortDraftMellin

theorem OAI.ShortDraftMellin.mobiusExpSum_flat_at_zero
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (b : ℝ) :
    (fun D : ℝ => mobiusExpSum χ D⁻¹) =O[𝓝[>] (0 : ℝ)]
      (fun D : ℝ => D ^ b) := by sorry
