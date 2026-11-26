-- Prove2me | Theorems.Thm_GRH_primitive_dirichlet_grids_outside_both_prefix_tests
-- name    : GRH.primitive_dirichlet_grids_outside_both_prefix_tests
-- status  : Open
-- author  : @scuba8684
-- created : 2026-11-26T16:15:57.520014+00:00
-- url     : https://prove2.me/theorems/1b3886ba-6475-4979-b196-63418759603e
-- title:
--   Primitive Dirichlet grids outside both the initial-gap and weighted-prefix arithmetic tests
-- statement:
--   For a primitive nonprincipal character and a target rectangle with right edge $b=0.8749570698$, height $H=h+1$, and left edge $a=1/2+(b-1/2)/H$, a finite Dirichlet-polynomial grid must pass if both the initial-gap period test and the weighted-prefix test fail. This is the remaining primitive-character assertion.
-- source:
--   Developed for the centered Möbius theorem at https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 and its open primitive grid condition at https://prove2.me/theorems/59bf325f-868f-5552-94bb-1b5f67435396. Uses the centered Abel estimate at https://prove2.me/theorems/3b5a3db7-3b41-46b5-a41d-4a78754ad8d2 and the power variation estimate at https://prove2.me/theorems/189b3afb-17f1-43b4-9047-0e36a164d965.

import Definitions.Def_GRH_DirichletGrid
import Definitions.Def_GRH_DirichletPeriod
import Definitions.Def_GRH_DirichletPrefix

theorem GRH.primitive_dirichlet_grids_outside_both_prefix_tests
    (d : ℕ) [NeZero d] (ψ : DirichletCharacter ℂ d) (hprim : ψ.IsPrimitive) (hψ : ψ ≠ 1)
    (h : ℕ) (hgap : ¬ GRH.DirichletPeriod.Covers d
      (1/2 + ((0.8749570698:ℝ)-1/2)/((h:ℝ)+1)) ((h:ℝ)+1))
    (hweight : ¬ GRH.DirichletPrefix.Covers d
      (1/2 + ((0.8749570698:ℝ)-1/2)/((h:ℝ)+1)) (0.8749570698:ℝ) ((h:ℝ)+1)) :
    ∃ m : ℕ, GRH.DirichletGrid.Passes ψ
      (1/2 + ((0.8749570698:ℝ)-1/2)/((h:ℝ)+1)) (0.8749570698:ℝ) ((h:ℝ)+1) m := by sorry
