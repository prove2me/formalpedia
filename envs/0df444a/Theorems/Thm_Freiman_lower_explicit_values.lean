-- Prove2me | Theorems.Thm_Freiman_lower_explicit_values
-- name    : Freiman.lower_explicit_values
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:15:00.898296+00:00
-- url     : https://prove2.me/theorems/a45b42ae-4976-4555-9b70-8abba3da7ddc
-- title:
--   Freiman lower construction: explicit values
-- statement:
--   (t : ℝ) (ht : lowerExplicitValue t) : lowerHasValue t
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, initial limit sequences

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_explicit_values (t : ℝ) (ht : lowerExplicitValue t) : lowerHasValue t := by
  sorry
