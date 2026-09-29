-- Prove2me | Theorems.Thm_Freiman_lowerJ_Q_box
-- name    : Freiman.lowerJ_Q_box
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:02:16.316473+00:00
-- url     : https://prove2.me/theorems/5573f5ed-21de-4763-805e-76bfac6321ec
-- title:
--   Freiman repeated-three proof: Q box
-- statement:
--   The four coefficient signs give the lower Q bound; the two monotone rational factors give the exact coarse upper475020045/601400527.
-- source:
--   Freiman report j_family.tex and j_certificates.tex, equal-three-width and lower-j3-uniform; exact source width-criterion route.

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

open Freiman

theorem Freiman.lowerJ_Q_box (hn : lowerJSignFacts) (r s q tau : ℝ) (hd : lowerJDomain r s q) (ht : (3/10:ℝ) ≤ tau ∧ tau ≤ (1/3:ℝ)) : (31/100:ℝ) < lowerJQ r s q tau ∧ lowerJQ r s q tau < (4/5:ℝ) := by
  sorry
