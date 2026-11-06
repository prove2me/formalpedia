-- Prove2me | Theorems.Thm_OAI_ShortDraftMellin_dirichlet_zero_free_of_mellin_bound
-- name    : OAI.ShortDraftMellin.dirichlet_zero_free_of_mellin_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:29:45.512194+00:00
-- url     : https://prove2.me/theorems/0993d781-a297-4a93-85fd-d587048abf9c
-- title:
--   Short Draft Mellin: dirichlet zero free of mellin bound
-- statement:
--   The Short Draft Mellin construction uses the dirichlet zero free of mellin bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/ExponentialSmoothing.lean#L407-L443
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Mellin/ExponentialSmoothing.lean#L407-L443

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

theorem OAI.ShortDraftMellin.dirichlet_zero_free_of_mellin_bound
    {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (σ : ℝ) (hσ : σ < 1)
    (A : ℝ → ℂ) (W : ℂ → ℂ)
    (hlocal : LocallyIntegrableOn A (Set.Ioi 0))
    (htop : A =O[atTop] (fun t : ℝ => t ^ σ))
    (hzero : A =ᶠ[𝓝[>] (0 : ℝ)] (fun _ => 0))
    (hW : Differentiable ℂ W)
    (heq : ∀ s : ℂ, 1 < s.re →
      χ.LFunction s * mellin A (-s) = W s)
    (ρ : ℂ) (hρ : σ < ρ.re) (hWρ : W ρ ≠ 0) :
    χ.LFunction ρ ≠ 0 := by sorry
