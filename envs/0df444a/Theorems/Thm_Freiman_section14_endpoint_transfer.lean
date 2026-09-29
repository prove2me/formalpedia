-- Prove2me | Theorems.Thm_Freiman_section14_endpoint_transfer
-- name    : Freiman.section14_endpoint_transfer
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T12:51:10.669715+00:00
-- url     : https://prove2.me/theorems/a48c21ca-4da2-47eb-8512-480027f82fd9
-- title:
--   Freiman §14: section14 endpoint transfer
-- statement:
--   Transfer the finite endpoint alternatives to the actual continued-fraction endpoint rules using the continuant determinant difference formula. The odd-left case uses the increasing local coordinate -t and swaps lower/upper endpoints; a virtual digit only defines an endpoint. This contains no finite sign search, which is supplied by the validated catalogue.
-- source:
--   Freiman report, active §14; Appendix Complete finite certificates for the scalar geometry of §14; full_readable_model.json.

import Definitions.Def_Freiman_section14Geometry
import Mathlib.Tactic.FinCases

open Freiman

theorem Freiman.section14_endpoint_transfer (p : LowerPair) (i : Fin 16) (pl : Section14Plan) (gs : ℕ × Section14Spec)
    (hm : lowerMixed p)
    (hmatch : section14Matches p (section14State section14Catalog (i.val+1)))
    (hv : section14StateValid section14Catalog (i.val+1))
    (hpl : pl ∈ (section14State section14Catalog (i.val+1)).plans) (hgs : gs ∈ pl.specs)
    (hc : ∀ j ∈ List.range (section14GoalBranches section14Catalog (section14Goal section14Catalog gs.1)).length,
      section14Holds (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).1 (section14R p) (section14S p) (section14Q p) →
      section14ComparisonHolds (section14Branch section14Catalog (section14Goal section14Catalog gs.1) j).2 (section14R p) (section14S p) (section14Q p)) : section14SpecHolds p gs.2 := by
  sorry
