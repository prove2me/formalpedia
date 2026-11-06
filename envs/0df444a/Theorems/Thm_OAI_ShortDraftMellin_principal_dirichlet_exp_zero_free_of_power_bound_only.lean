-- Prove2me | Theorems.Thm_OAI_ShortDraftMellin_principal_dirichlet_exp_zero_free_of_power_bound_only
-- name    : OAI.ShortDraftMellin.principal_dirichlet_exp_zero_free_of_power_bound_only
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:14:18.09113+00:00
-- url     : https://prove2.me/theorems/269b1b56-c6da-4261-a084-3823df995f3e
-- title:
--   Short Draft Mellin: principal dirichlet exp zero free of power bound only
-- statement:
--   The Short Draft Mellin construction uses the principal dirichlet exp zero free of power bound only property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LogProfiles.lean#L91-L143
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/LogProfiles.lean#L91-L143

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

theorem OAI.ShortDraftMellin.principal_dirichlet_exp_zero_free_of_power_bound_only
    (q : ℕ) [NeZero q]
    (σ : ℝ) (hσpos : 0 < σ) (hσ : σ < 1)
    (htop : (fun D : ℝ => mobiusExpSum
        (1 : DirichletCharacter ℂ q) D⁻¹) =O[atTop]
      (fun D : ℝ => D ^ σ))
    (ρ : ℂ) (hρ : σ < ρ.re) (hρone : ρ ≠ 1) :
    DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) ρ ≠ 0 := by sorry
