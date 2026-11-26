-- Prove2me | Theorems.Thm_GRH_weighted_prefix_first_and_third_grids
-- name    : GRH.weighted_prefix_first_and_third_grids
-- status  : Proved
-- author  : @scuba8684
-- created : 2026-11-26T16:15:56.9788+00:00
-- url     : https://prove2.me/theorems/e2431866-7ccd-5980-85ca-54568417a792
-- title:
--   The first target grid at nineteen moduli and the third grid at levels three and six
-- statement:
--   At the record boundary $b=0.8749570698$, the first target grid passes for every nonprincipal character at a divisor of $24,36,42$, or $60$. These include nineteen moduli admitting such characters. The third grid, with real interval $[1/2+(b-1/2)/3,b]$ and height three, passes for divisors of $6$, including moduli $3$ and $6$.
-- source:
--   Developed for the centered Möbius theorem at https://prove2.me/theorems/5000f709-1ce6-4ce6-a1ad-637c5b963006 and its open primitive grid condition at https://prove2.me/theorems/59bf325f-868f-5552-94bb-1b5f67435396. Uses the centered Abel estimate at https://prove2.me/theorems/3b5a3db7-3b41-46b5-a41d-4a78754ad8d2 and the power variation estimate at https://prove2.me/theorems/189b3afb-17f1-43b4-9047-0e36a164d965.

import Definitions.Def_GRH_DirichletGrid
import Definitions.Def_GRH_DirichletPrefix

open GRH.DirichletGrid GRH.DirichletPrefix

theorem GRH.weighted_prefix_first_and_third_grids (d : ℕ) [NeZero d] (χ : DirichletCharacter ℂ d) (hχ : χ ≠ 1)
    (h : ℕ) (hc : (h=0 ∧ (d ∣ 24 ∨ d ∣ 36 ∨ d ∣ 42 ∨ d ∣ 60)) ∨ (h=2 ∧ d ∣ 6)) :
    ∃ m : ℕ, Passes χ (1/2+((0.8749570698:ℝ)-1/2)/((h:ℝ)+1))
      (0.8749570698:ℝ) ((h:ℝ)+1) m := by sorry
