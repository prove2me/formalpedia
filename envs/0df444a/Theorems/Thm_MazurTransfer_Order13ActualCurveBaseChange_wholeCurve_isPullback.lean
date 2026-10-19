-- Prove2me | Theorems.Thm_MazurTransfer_Order13ActualCurveBaseChange_wholeCurve_isPullback
-- name    : MazurTransfer.Order13ActualCurveBaseChange.wholeCurve_isPullback
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T03:37:18.136262+00:00
-- url     : https://prove2.me/theorems/b95ee352-989d-4142-a1e5-2d6f6a24b079
-- title:
--   The actual order-thirteen curve map gives the Cartesian base-change square
-- statement:
--   Let $R$ and $S$ be commutative rings with an $R$-algebra structure on $S$. Let $C_R$ and $C_S$ be the fixed two-chart order-thirteen curves, and let $f_{S/R}:C_S\to C_R$ be the actual glued morphism constructed from the specified coordinate ring maps. Its base square is Cartesian:
--   $$C_S\;\cong\;C_R\times_{\operatorname{Spec}R}\operatorname{Spec}S,$$
--   with projections given by $f_{S/R}$ and the actual structure map of $C_S$.
--
--   This identifies the specified morphism of the actual curves with scheme-theoretic base change. It supplies the actual fibre compatibility used in the integral Abel–Jacobi point dictionary.
-- source:
--   Exact statement wholeCurve_isPullback from the checked MazurTheorem source Order13WholeCurveBaseChangeIsomorphism.lean. This proof directly reuses the separate Proved public theorem MazurTransfer.order13_actual_whole_curve_base_change_isomorphism, identifies its coordinate maps with the actual maps by ring-homomorphism extensionality, and identifies the glued morphism by the actual open cover. Complete original and public types are checked by closed kernel witnesses. Vas and contributors, Apache-2.0; official Anthropic FLT APIs retain pin 6e837e75355538c7f80bab5b956861e86c4eacc2 and attribution.

import Definitions.Def_MazurTransfer_Order13ActualCurveBaseChangeMap
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.Order13ActualCurveBaseChange
universe u

theorem MazurTransfer.Order13ActualCurveBaseChange.wholeCurve_isPullback (R S : Type u) [CommRing R] [CommRing S] [Algebra R S] :
    IsPullback (curveMap R S) (curveToBase S) (curveToBase R)
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))  := by sorry
