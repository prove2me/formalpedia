-- Prove2me | Theorems.Thm_OAI_ShortDraftMellin_dirichlet_exp_zero_free_of_power_bound_only
-- name    : OAI.ShortDraftMellin.dirichlet_exp_zero_free_of_power_bound_only
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:14:12.067204+00:00
-- url     : https://prove2.me/theorems/dfe11351-040c-4316-91f6-7f9ba3d50138
-- title:
--   Short Draft Mellin: dirichlet exp zero free of power bound only
-- statement:
--   The Short Draft Mellin construction uses the dirichlet exp zero free of power bound only property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LogProfiles.lean#L81-L89
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LogProfiles.lean#L81-L89

import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_ExponentialSmoothing
import Definitions.Def_OAI_NumberTheory_DirichletL_Mellin_LogProfiles
set_option autoImplicit false
open OAI
open scoped BigOperators
open MulChar AddChar
open scoped BigOperators
open Filter Asymptotics MeasureTheory
open scoped Topology
open OAI.ShortDraftMellin

theorem OAI.ShortDraftMellin.dirichlet_exp_zero_free_of_power_bound_only
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1)
    (σ : ℝ) (hσpos : 0 < σ) (hσ : σ < 1)
    (htop : (fun D : ℝ => mobiusExpSum χ D⁻¹) =O[atTop]
      (fun D : ℝ => D ^ σ))
    (ρ : ℂ) (hρ : σ < ρ.re) : χ.LFunction ρ ≠ 0 := by sorry
