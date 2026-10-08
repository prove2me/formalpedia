-- Prove2me | Theorems.Thm_MazurCampaign_no_prime_ge_seventeen
-- name    : MazurCampaign.no_prime_ge_seventeen
-- status  : Open
-- author  : @Vas
-- created : 2026-10-06T08:32:48.226514+00:00
-- url     : https://prove2.me/theorems/2b51c68a-3121-4d24-b415-7b7c1574c4ba
-- title:
--   No rational torsion of prime order at least seventeen
-- statement:
--   For every elliptic curve $E/\mathbb Q$ and every prime $p\ge17$, no rational torsion point has exact order $p$: $$\forall P\in E(\mathbb Q)_{\mathrm{tors}},\quad\operatorname{ord}(P)\ne p.$$ This is the general elliptic-curve prime-order exclusion required by the full Mazur mission. The curve hypothesis is only ellipticity.
-- source:
--   https://github.com/vilin97/MazurTheorem/blob/54d43d8dda8a6fcf069cc02a815f850d762c5c0c/MazurTorsion/Arithmetic/PointOrder.lean

import Mathlib
import Definitions.Def_MazurCampaign_group_constraints

theorem MazurCampaign.no_prime_ge_seventeen
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ∀ p : ℕ, p.Prime → 17 ≤ p →
      ∀ x : MazurCampaign.RationalTorsion E, addOrderOf x ≠ p := by sorry
