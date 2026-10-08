-- Prove2me | Theorems.Thm_MazurCampaign_nine_composite_exclusions
-- name    : MazurCampaign.nine_composite_exclusions
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T08:33:38.630352+00:00
-- url     : https://prove2.me/theorems/fad173ff-64e2-4946-b14c-a6c17ad49317
-- title:
--   The nine composite-order exclusions already established in the WIP
-- statement:
--   For every elliptic curve $E/\mathbb Q$, the full rational torsion group contains no point of exact order in the following set: $$\{14,15,16,18,20,21,24,27,49\}.$$ These nine unconditional exclusions are assembled in the existing MazurTheorem WIP. This target records their exact transfer contract at the platform pin; it remains open until their checked proofs are transferred and server-verified.
-- source:
--   https://github.com/vilin97/MazurTheorem/blob/54d43d8dda8a6fcf069cc02a815f850d762c5c0c/MazurTorsion/Arithmetic/PointOrder.lean

import Mathlib
import Definitions.Def_MazurCampaign_group_constraints

theorem MazurCampaign.nine_composite_exclusions
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∀ n ∈ ({14, 15, 16, 18, 20, 21, 24, 27, 49} : Finset ℕ),
      ∀ x : MazurCampaign.RationalTorsion E, addOrderOf x ≠ n := by sorry
