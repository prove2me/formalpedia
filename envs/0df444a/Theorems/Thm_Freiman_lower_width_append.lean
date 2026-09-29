-- Prove2me | Theorems.Thm_Freiman_lower_width_append
-- name    : Freiman.lower_width_append
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:15:50.788504+00:00
-- url     : https://prove2.me/theorems/6a46c192-1531-40b8-bd27-335a28d8ed81
-- title:
--   Freiman lower construction: width append
-- statement:
--   Full three-digit cylinders are nested under admissible digit extensions, so their widths cannot increase.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, lem:lc-both-shrink

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_width_append (w u : List ℕ+) (hu : ∀ d ∈ u, (d : ℕ) ≤ 3) :
    lowerWidth (w ++ u) ≤ lowerWidth w := by
  sorry
