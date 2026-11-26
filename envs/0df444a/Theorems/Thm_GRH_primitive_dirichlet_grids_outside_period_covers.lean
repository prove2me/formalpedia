-- Prove2me | Theorems.Thm_GRH_primitive_dirichlet_grids_outside_period_covers
-- name    : GRH.primitive_dirichlet_grids_outside_period_covers
-- status  : Open
-- author  : @scuba8684
-- created : 2026-11-26T15:34:27.028+00:00
-- url     : https://prove2.me/theorems/59bf325f-868f-5552-94bb-1b5f67435396
-- title:
--   Primitive Dirichlet grid certificates outside the arithmetic period test
-- statement:
--   Put $b=0.8749570698$. For every primitive nonprincipal character modulo $d$ and natural $h$, write $H=h+1$ and $a=1/2+(b-1/2)/H$. If the arithmetic period test does not cover $d,a,H$, a finite Dirichlet-polynomial grid must pass on $[a,b]\times[-H,H]$. This is the remaining open primitive-character assertion.
-- source:
--   Developed for the centered Möbius bound at https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 and its primitive grid condition at https://prove2.me/theorems/a7f725ef-ecef-5ae2-855e-fc5b2d31cf0a. The centered-prefix estimate uses the published power variation bound at https://prove2.me/theorems/189b3afb-17f1-43b4-9047-0e36a164d965 and Dirichlet tail estimate at https://prove2.me/theorems/f1d91210-556c-47bf-8726-5a67ca5f667f.

import Definitions.Def_GRH_DirichletGrid
import Definitions.Def_GRH_DirichletPeriod

theorem GRH.primitive_dirichlet_grids_outside_period_covers
    (d : ℕ) [NeZero d] (ψ : DirichletCharacter ℂ d) (hprim : ψ.IsPrimitive) (hψ : ψ ≠ 1)
    (h : ℕ) (hremaining : ¬ GRH.DirichletPeriod.Covers d
      (1/2 + ((0.8749570698:ℝ)-1/2)/((h:ℝ)+1)) ((h:ℝ)+1)) :
    ∃ m : ℕ, GRH.DirichletGrid.Passes ψ
      (1/2 + ((0.8749570698:ℝ)-1/2)/((h:ℝ)+1)) (0.8749570698:ℝ) ((h:ℝ)+1) m := by sorry
