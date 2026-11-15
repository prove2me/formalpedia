-- Prove2me | Theorems.Thm_MazurP23_exists_point_of_rationalTorsion
-- name    : MazurP23.exists_point_of_rationalTorsion
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-15T02:40:32.469322+00:00
-- url     : https://prove2.me/theorems/ac518003-7893-4395-8216-16505eac4008
-- title:
--   A rational torsion point of order p gives affine coordinates
-- statement:
--   If E(Q) has a torsion point of prime order p, then there are rational x, y on E with Point.some x y of additive order p.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/6e837e75355538c7f80bab5b956861e86c4eacc2/P2M/Sol/S_FreyPackage_frey_no_cofixed_large.lean

import Mathlib
import Definitions.Def_EllipticCurve_ZeroComponentAt
import Definitions.Def_FLTPrelim_GaloisRep
import Definitions.Def_FLTPrelim_Ramification
import Definitions.Def_FLTPrelim_CofixedLine
import Definitions.Def_MazurCampaign_target_objects

set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open WeierstrassCurve WeierstrassCurve.Affine WeierstrassCurve.Affine.Point
open scoped WeierstrassCurve.Affine NNReal

namespace MazurP23
theorem exists_point_of_rationalTorsion (E : WeierstrassCurve ℚ) {p : ℕ} (x : MazurCampaign.RationalTorsion E) (hx : addOrderOf x = p) : ∃ P : (E⁄ℚ).Point, addOrderOf P = p := by sorry
end MazurP23
