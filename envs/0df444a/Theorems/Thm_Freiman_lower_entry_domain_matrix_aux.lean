-- Prove2me | Theorems.Thm_Freiman_lower_entry_domain_matrix_aux
-- name    : Freiman.lower_entry_domain_matrix_aux
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:20:54.998335+00:00
-- url     : https://prove2.me/theorems/f64982f2-7048-416a-aa25-cf4cf827fe7b
-- title:
--   Freiman lower construction: entry domain matrix aux
-- statement:
--   The six remaining strict multiaffine inequalities for auxiliary B, using the actual positive n+1 period factor.
-- source:
--   Freiman's Hall ray: Proof report and corrected English text (8 September 2026), parts/lower_core.tex, prop:lc-H-entry; source H certificate appendix

import Definitions.Def_Freiman_lowerInitialEntry
import Definitions.Def_Freiman_lowerCertificates
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push

open Freiman

theorem Freiman.lower_entry_domain_matrix_aux (x : ℝ) (hx : x ∈ Set.Icc (0:ℝ) (1/85)) : lowerEntryMatrixBounds (lowerEntryAuxMatrices x) := by
  sorry
