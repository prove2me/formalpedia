-- Prove2me | Theorems.Thm_MajorityDepthThree_Exact_packing_covering_bridge
-- name    : MajorityDepthThree.Exact.packing_covering_bridge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T11:23:47.852643+00:00
-- url     : https://prove2.me/theorems/f36e1dc7-8ca8-40cd-b416-96edcca1d497
-- title:
--   Section 4.1, concluding display after (P) — attained dual reduction
-- statement:
--   Let $F=G\wedge H$ be a valid $t$-threshold 3-CNF on $V$, with $H$ its entire positive part, still on $V$. Fix $R>0$ and set $Q=(2R)^{-1}$. Let $D_H=D_{T(H)}(R)$ be the packing maximum (DLP-2), and $C_H=C_{T(H)}(R,Q)$ the covering minimum (P). Then
--
--   $$\theta_t(F)R^t\le Z(F,R)\le D_H=C_H.$$
--
--   Both programs have feasible weights attaining their respective values; the packing objectives are bounded above and the covering objectives bounded below. Thus the equality is of attained finite optima. These statements are conclusions, with no assumed LP budget. This is the source's reduction from signed counting to a program determined solely by the monotone part.
--
--   Differences from the source:
--   - encoding: A finite ground set V and its subsets → Finite subsets V of a variable type, with finite families of subsets; reason: Every source instance has this representation; all assignments and ambient isolated variables are retained
--   - encoding: Attained finite maxima and minima → Real sSup and sInf, with optimal feasible witnesses, equality to their values and objective boundedness in the conclusion; reason: This explicitly proves the well-posedness used by the source instead of assuming it
-- source:
--   Mohit Gurumukhani, Daniel Kleber, Ramamohan Paturi, Christopher Rosin, Michael Saks, Navid Talebanfard, STOC 2027 submission #677 (October 2026), p.12, Section 4.1, concluding display after (P) and preceding attainment sentence

import Definitions.Def_MajorityDepthThree_Exact_Restrictions
import Definitions.Def_MajorityDepthThree_Exact_Circuits

set_option autoImplicit false

namespace MajorityDepthThree.Exact

theorem packing_covering_bridge {α : Type} [DecidableEq α] (V : Finset α)
    (F : CNF α) (t : ℕ) (hv : ValidCNF V F) (hw : Width 3 F)
    (ht : Threshold V F t) (R : ℝ) (hR : 0 < R) :
    let A := transversals V (positivePart F)
    let Q := (2 * R)⁻¹
    (theta V F t : ℝ) * R ^ t ≤ partitionSum V F R ∧
    partitionSum V F R ≤ packingValue A R ∧
    packingValue A R = coverValue A R Q ∧
    (∃ f, PackingOptimal A R f ∧ cost A R f = packingValue A R) ∧
    (∃ f, CoverOptimal A R Q f ∧ cost A R f = coverValue A R Q) ∧
    BddAbove {v : ℝ | ∃ f, PackingFeasible A f ∧ cost A R f = v} ∧
    BddBelow {v : ℝ | ∃ f, CoverFeasible A Q f ∧ cost A R f = v} := by sorry

end MajorityDepthThree.Exact
