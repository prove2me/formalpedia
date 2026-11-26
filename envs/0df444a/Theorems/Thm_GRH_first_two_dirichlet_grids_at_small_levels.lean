-- Prove2me | Theorems.Thm_GRH_first_two_dirichlet_grids_at_small_levels
-- name    : GRH.first_two_dirichlet_grids_at_small_levels
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T15:34:19.599978+00:00
-- url     : https://prove2.me/theorems/1995bdfc-c232-4d82-801e-b715f6d79d9a
-- title:
--   The first required Dirichlet grids at eleven moduli and the second grids at three moduli
-- statement:
--   For every nonprincipal character of modulus $3,4,5,6,8,9,10,12,15,18$, or $30$, the first finite grid in the primitive-character reduction of the centered Möbius bound passes. Its real coordinate is $0.8749570698$ and its height is one. For moduli $3,4,6$, the second grid passes as well, with real interval $[0.6874785349,0.8749570698]$ and height two. The formal statement covers every divisor of the specified witness moduli.
-- source:
--   Developed for the centered Möbius bound at https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 and its primitive grid condition at https://prove2.me/theorems/a7f725ef-ecef-5ae2-855e-fc5b2d31cf0a. The centered-prefix estimate uses the published power variation bound at https://prove2.me/theorems/189b3afb-17f1-43b4-9047-0e36a164d965 and Dirichlet tail estimate at https://prove2.me/theorems/f1d91210-556c-47bf-8726-5a67ca5f667f.

import Definitions.Def_GRH_DirichletGrid
import Definitions.Def_GRH_DirichletPeriod

open GRH.DirichletGrid GRH.DirichletPeriod

theorem GRH.first_two_dirichlet_grids_at_small_levels (d : ℕ) [NeZero d] (ψ : DirichletCharacter ℂ d) (hψ : ψ ≠ 1)
    (h : ℕ) (hcase : (h=0 ∧ (d ∣ 8 ∨ d ∣ 12 ∨ d ∣ 18 ∨ d ∣ 30)) ∨
      (h=1 ∧ (d ∣ 4 ∨ d ∣ 6))) :
    ∃ m : ℕ, GRH.DirichletGrid.Passes ψ
      (1/2 + ((0.8749570698:ℝ)-1/2)/((h:ℝ)+1)) (0.8749570698:ℝ) ((h:ℝ)+1) m := by sorry
