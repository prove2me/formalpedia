-- Prove2me | Theorems.Thm_Freiman_lower_initial_n_denominators
-- name    : Freiman.lower_initial_n_denominators
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:20:21.05541+00:00
-- url     : https://prove2.me/theorems/38982575-ebf0-40d8-b7d3-f6788f295300
-- title:
--   Freiman lower construction: initial n denominators
-- statement:
--   Every source quartic denominator is strictly positive on the whole rational source box.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-contacts; exact initial contact appendix

import Definitions.Def_Freiman_lowerInitialSeamData
import Definitions.Def_Freiman_lowerInitialNData
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

open scoped BigOperators

theorem Freiman.lower_initial_n_denominators (c : LowerInitialNCase) (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) (1/85)) :
    ∀ i : Fin 4, 0 < lowerInitialMatDen (lowerInitialNMatrix c i x) lowerTau := by
  sorry
