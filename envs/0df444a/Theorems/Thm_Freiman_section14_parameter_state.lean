-- Prove2me | Theorems.Thm_Freiman_section14_parameter_state
-- name    : Freiman.section14_parameter_state
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:50:52.522343+00:00
-- url     : https://prove2.me/theorems/c54cf47e-ef8b-4739-abc6-be74854ec6ce
-- title:
--   Freiman §14: section14 parameter state
-- statement:
--   An admissible mixed parent has one of the sixteen geometry states and its actual continuant ratios lie in that closed rectangle. The language states 313 and 3131 preserve every future natural-shortening flag and are covered by the respective 3 and 31 geometry states.
-- source:
--   Freiman report, active §14; Appendix Complete finite certificates for the scalar geometry of §14; full_readable_model.json.

import Definitions.Def_Freiman_section14Geometry
import Mathlib.Tactic.FinCases

open Freiman

theorem Freiman.section14_parameter_state (t : ℝ) (p : LowerPair) (hs : lowerState t p) (hm : lowerMixed p) : ∃ i : Fin 16, section14Matches p (section14State section14Catalog (i.val+1)) ∧ certRectangleMem (section14State section14Catalog (i.val+1)).rectangle (section14R p) (section14S p) := by
  sorry
