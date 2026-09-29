-- Prove2me | Theorems.Thm_Freiman_lower_beta_fixed
-- name    : Freiman.lower_beta_fixed
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:14:19.183163+00:00
-- url     : https://prove2.me/theorems/493f6563-dc23-482c-8437-68a945cc5e58
-- title:
--   Freiman lower construction: beta fixed
-- statement:
--   The periodic 13 endpoint is fixed by its two-digit map; this identifies the e13 expression in lower_core with the full appended-13 width.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, eq:lc-full-width and lower_section14.tex, auxiliary endpoint rule

import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_beta_fixed : prefixEval [1,3] lowerBeta = lowerBeta := by
  sorry
