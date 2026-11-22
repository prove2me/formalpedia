-- Prove2me | Theorems.Thm_GJKKL_card_matchingsOfSize_ge
-- name    : GJKKL.card_matchingsOfSize_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:50:52.990222+00:00
-- url     : https://prove2.me/theorems/9c3ad08a-2d19-4aed-9cb7-3b632db14c95
-- title:
--   GJKKL: card matchings Of Size ge
-- statement:
--   The counting step in quotient form: `#matchings ≥ P[T*(m)] · ∏_{i<m} g i / m!`.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Counting.lean#L102-L107
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Counting.lean#L102-L107

module
public import Definitions.Def_GJKKL_Greedy_Process
public import Definitions.Def_GJKKL_History_Freedman
public import Definitions.Def_GJKKL_Greedy_Counting
set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset History
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem GJKKL.card_matchingsOfSize_ge (H : Finset (Finset V)) (hne : ∀ e ∈ H, e.Nonempty)
    (g : ℕ → ℝ) (hg : ∀ i, 0 ≤ g i) (m : ℕ) :
    prob (greedyKernel H) m (ManyAvail H g) * (∏ i ∈ range m, g i) / m.factorial ≤
      (matchingsOfSize H m).card := by sorry
