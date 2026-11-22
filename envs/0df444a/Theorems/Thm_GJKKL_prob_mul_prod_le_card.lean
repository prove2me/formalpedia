-- Prove2me | Theorems.Thm_GJKKL_prob_mul_prod_le_card
-- name    : GJKKL.prob_mul_prod_le_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:50:46.864802+00:00
-- url     : https://prove2.me/theorems/97bcacaa-f429-482f-91a0-11e138ad7c08
-- title:
--   GJKKL: prob mul prod le card
-- statement:
--   **Counting step** ((8.15) of GJKKL): `P[T*(m)] · ∏_{i<m} g i ≤ m! · #matchings`.
--
--   Source: https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Counting.lean#L79-L99
-- source:
--   https://github.com/jtraverso/gjkkl-matching-count/blob/2d51367b7777a669de247e10b5e93229c8e06f1c/GJKKL/Greedy/Counting.lean#L79-L99

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

theorem GJKKL.prob_mul_prod_le_card (H : Finset (Finset V)) (hne : ∀ e ∈ H, e.Nonempty)
    (g : ℕ → ℝ) (hg : ∀ i, 0 ≤ g i) (m : ℕ) :
    prob (greedyKernel H) m (ManyAvail H g) * ∏ i ∈ range m, g i ≤
      (m.factorial : ℝ) * (matchingsOfSize H m).card := by sorry
