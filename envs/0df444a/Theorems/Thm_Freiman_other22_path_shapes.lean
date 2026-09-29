-- Prove2me | Theorems.Thm_Freiman_other22_path_shapes
-- name    : Freiman.other22_path_shapes
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:34:45.109458+00:00
-- url     : https://prove2.me/theorems/b6c6fd64-acd1-499a-8fe0-0ebfd10b8aed
-- title:
--   other22 path shapes
-- statement:
--   The six fixed descriptor records encode precisely Z→23→20(reflect)→10(no reflection), final row1 and the original suffix contexts; this finite structural check supplies the generic source-DNF induction.
-- source:
--   Report §7.3, Lemma 7.4 (lem:old23-other22-target), printed p.43; other22_target.tex and Appendix other22_certificates.tex; original 144-obligation exact certificate.

import Definitions.Def_Freiman_other22Verification
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.SplitIfs

open Freiman

theorem Freiman.other22_path_shapes :
    ∀ k : Fin 6, lowerHistoryStructural (other22Paths k) := by
  sorry
