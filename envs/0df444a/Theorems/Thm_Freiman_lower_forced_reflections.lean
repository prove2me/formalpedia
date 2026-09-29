-- Prove2me | Theorems.Thm_Freiman_lower_forced_reflections
-- name    : Freiman.lower_forced_reflections
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:15:50.364991+00:00
-- url     : https://prove2.me/theorems/e4c16031-43c8-44a7-8ab9-b03275fb05cb
-- title:
--   Freiman lower construction: forced reflections
-- statement:
--   Four distinct full-width inequalities from the defining fork contact. They force reflection after 2,3,11 and retain the wider side after the opposite-parity 0,1 exception.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/forced_reflections.tex, lem:lc-forced-reflections

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_forced_reflections (p : LowerPair) (hg : lowerGood p) (hb : lowerParameterBox p) :
    let q := lowerNormalize p
    lowerWidth (q.1 ++ [2]) < lowerWidth q.2 ∧
    lowerWidth (q.1 ++ [3]) < lowerWidth q.2 ∧
    lowerWidth (q.1 ++ [1,1]) < lowerWidth q.2 ∧
    lowerWidth (q.2 ++ [1]) < lowerWidth q.1 := by
  sorry
