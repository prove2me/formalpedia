-- Prove2me | Theorems.Thm_GJKKL_History_freedman_super
-- name    : GJKKL.History.freedman_super
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:37:21.583386+00:00
-- url     : https://prove2.me/theorems/3c82c876-0424-4b89-841b-04311ae51be2
-- title:
--   History: freedman super
-- statement:
--   **Freedman's inequality** for stopped supermartingales on a finite history tree.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/Freedman.lean#L148-L231
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/History/Freedman.lean#L148-L231

module
public import Definitions.Def_GJKKL_History_Basic
public import Definitions.Def_RequestProject_Pseudorandom_Bernstein
public import Definitions.Def_GJKKL_History_Freedman
set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.History
open Finset
variable {α : Type*} [Fintype α] [DecidableEq α]
variable (κ : Kernel α) (X : List α → ℝ) (G : List α → Prop)

theorem GJKKL.History.freedman_super (T : ℕ) (C s lam : ℝ) (hC : 0 < C) (hs : 0 < s) (hlam : 0 < lam)
    (htrend : ∀ h : List α, h.length < T → AliveBefore G h → G h →
      ∑ a, κ.K h a * (X (a :: h) - X h) ≤ 0)
    (hinc : ∀ h : List α, h.length < T → AliveBefore G h → G h →
      ∀ a, κ.K h a ≠ 0 → |X (a :: h) - X h| ≤ C)
    (hacc : ∀ h : List α, h.length < T → AliveBefore G h → G h → accSum κ X h ≤ s) :
    prob κ T (fun h => lam ≤ X h - X [] ∧ AliveBefore G h) ≤
      Real.exp (-(lam ^ 2 / (2 * C * (lam + s)))) := by sorry
