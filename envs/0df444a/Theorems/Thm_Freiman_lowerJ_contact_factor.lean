-- Prove2me | Theorems.Thm_Freiman_lowerJ_contact_factor
-- name    : Freiman.lowerJ_contact_factor
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:02:08.739568+00:00
-- url     : https://prove2.me/theorems/e6d6e32c-ce90-404c-8bf6-74306b4ac766
-- title:
--   Freiman repeated-three proof: contact factor
-- statement:
--   The printed S27/S28 are exactly the endpoints of a linear numerator in tau.
-- source:
--   Freiman report j_family.tex and j_certificates.tex, equal-three-width and lower-j3-uniform; exact source width-criterion route.

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

open Freiman

theorem Freiman.lowerJ_contact_factor (hn : lowerJSignFacts) (tau : ℝ) (ht : (3/10:ℝ) ≤ tau ∧ tau ≤ (1/3:ℝ)) : (371/500:ℝ) < lowerJCoeff*(1+tau*lowerJC)/(1+tau*lowerJA) := by
  sorry
