-- Prove2me | Theorems.Thm_Freiman_lower_parameter_normalize
-- name    : Freiman.lower_parameter_normalize
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:18:04.583486+00:00
-- url     : https://prove2.me/theorems/265b38d3-eedc-4b9e-a5ad-82771d53afac
-- title:
--   Freiman lower construction: parameter normalize
-- statement:
--   Exchanging the two actual outward words preserves the symmetric [1/4,4/5] parameter domain.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, full-width normalization

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_parameter_normalize (p : LowerPair) (hp : lowerParameterBox p) : lowerParameterBox (lowerNormalize p) := by
  sorry
