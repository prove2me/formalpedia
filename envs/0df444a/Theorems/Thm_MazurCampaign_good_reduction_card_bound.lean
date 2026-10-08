-- Prove2me | Theorems.Thm_MazurCampaign_good_reduction_card_bound
-- name    : MazurCampaign.good_reduction_card_bound
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-06T08:21:05.550445+00:00
-- url     : https://prove2.me/theorems/7f80f820-ad30-4ca2-803f-69e9cacbd186
-- title:
--   Full rational torsion injects at an odd good prime
-- statement:
--   Let $W$ be an integral Weierstrass model whose rational base change $E/\mathbb Q$ is elliptic. Let $p>2$ be prime and suppose $p\nmid\Delta(W)$. Then the full rational torsion group is finite and its order divides the number of points on the reduction: $$ E(\mathbb Q)_{\mathrm{tors}}\text{ is finite},\qquad \#E(\mathbb Q)_{\mathrm{tors}}\mid\#\widetilde W(\mathbb F_p). $$ This is a bound on the entire torsion group, including its p-primary part, at an unramified odd good prime. It supplies the upper bounds used by the fifteen explicit occurrence witnesses in the full Mazur torsion mission.
-- source:
--   https://github.com/vilin97/MazurTheorem/blob/54d43d8dda8a6fcf069cc02a815f850d762c5c0c/EllipticCurves/ReductionAtPrime.lean

import Definitions.Def_MazurCampaign_group_constraints

theorem MazurCampaign.good_reduction_card_bound
    (W : WeierstrassCurve ℤ) (p : ℕ) [Fact p.Prime]
    [(W.map (Int.castRingHom ℚ)).IsElliptic]
    (hp : 2 < p) (hgood : ¬ (p : ℤ) ∣ W.Δ) :
    Finite (MazurCampaign.RationalTorsion (W.map (Int.castRingHom ℚ))) ∧
      Nat.card (MazurCampaign.RationalTorsion (W.map (Int.castRingHom ℚ))) ∣
        Nat.card (W.map (Int.castRingHom (ZMod p))).toAffine.Point := by sorry
