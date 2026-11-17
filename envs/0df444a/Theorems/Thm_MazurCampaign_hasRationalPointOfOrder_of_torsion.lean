-- Prove2me | Theorems.Thm_MazurCampaign_hasRationalPointOfOrder_of_torsion
-- name    : MazurCampaign.hasRationalPointOfOrder_of_torsion
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:07:04.182291+00:00
-- url     : https://prove2.me/theorems/e93895da-bfb6-4c1e-ad33-21487262dd1b
-- title:
--   A rational torsion point of exact order $n$ gives a rational point of order $n$
-- statement:
--   Let $E/ℚ$ be an elliptic curve, let $x∈E(ℚ)_{tors}$, and let $n∈ℕ$. If the additive order of $x$ is $n$, then $$E\text{ has a rational point of exact order }n.$$ This bridges the campaign's torsion subtype to the predicate used by the Tate-normal-form reduction.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_MazurCampaign_group_constraints
import Definitions.Def_TorsionDefs

open scoped WeierstrassCurve.Affine
open MazurCampaign

theorem MazurCampaign.hasRationalPointOfOrder_of_torsion
    (E : WeierstrassCurve ℚ) [E.IsElliptic]
    (x : RationalTorsion E) (n : ℕ) (hx : addOrderOf x = n) :
    MazurProof.HasRationalPointOfOrder E n := by sorry
