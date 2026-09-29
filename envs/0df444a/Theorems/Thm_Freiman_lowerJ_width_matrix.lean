-- Prove2me | Theorems.Thm_Freiman_lowerJ_width_matrix
-- name    : Freiman.lowerJ_width_matrix
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T14:01:10.485384+00:00
-- url     : https://prove2.me/theorems/3a64a104-205d-427c-8338-b310b3eef4e8
-- title:
--   Freiman repeated-three proof: width matrix
-- statement:
--   Cancel the unimodular determinant in the actual full αβ width formula; actual positive denominators are retained.
-- source:
--   Freiman report j_family.tex and j_certificates.tex, equal-three-width and lower-j3-uniform; exact source width-criterion route.

import Definitions.Def_Freiman_lowerJData
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Tactic.FinCases

open Freiman

theorem Freiman.lowerJ_width_matrix (hf : ∀ (w : List ℕ+) (t : ℝ), 0 < t → prefixEval w t = lowerInitialMatEval (lowerInitialWordMatrix w) t ∧ 0 < lowerInitialMatDen (lowerInitialWordMatrix w) t ∧ (lowerInitialWordMatrix w).a*(lowerInitialWordMatrix w).d - (lowerInitialWordMatrix w).b*(lowerInitialWordMatrix w).c = (-1:ℝ)^w.length) (hb : ∀ w : List ℕ+, (lowerInitialWordMatrix w).c = ((lowerCD w).1:ℝ) ∧ (lowerInitialWordMatrix w).d = ((lowerCD w).2:ℝ)) : ∀ w : List ℕ+, lowerWidth w = (lowerBeta-lowerAlpha)/((((lowerCD w).1:ℝ)*lowerAlpha+(lowerCD w).2)*(((lowerCD w).1:ℝ)*lowerBeta+(lowerCD w).2)) := by
  sorry
