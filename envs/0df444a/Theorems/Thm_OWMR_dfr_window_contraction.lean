-- Prove2me | Theorems.Thm_OWMR_dfr_window_contraction
-- name    : OWMR.dfr_window_contraction
-- status  : Proved
-- author  : @Ming Hu
-- created : 2026-11-17T09:57:14.219446+00:00
-- url     : https://prove2.me/theorems/d730cfbb-3caa-4c5c-b6fe-282674b4db96
-- title:
--   Lemma D.1 on renewal windows: a shortened window contracts the mirror cost by $t$ and does not raise holding and backlog cost
-- statement:
--   Fix retailer $i$ of a network under the standing assumptions, with renewal measure $U$ of its demand. Let $0<w\le\hat w$ and $0<t\le1$ satisfy $U[0,w)=t\,U[0,\hat w)$, and suppose $x\mapsto U[0,x]$ is concave on $[0,\hat w]$. Then:
--
--   1. (mirror contraction) for all reals $S$ and $\hat S$, $\mathrm{mirrorCost}_i(S-w,S)\le t\,\mathrm{mirrorCost}_i(\hat S-\hat w,\hat S)$;
--   2. (holding and backlog) for every $\hat S$ there is a target $S$ with $c_i(F_i;0,S-w,S)\le c_i(F_i;0,\hat S-\hat w,\hat S)$,
--
--   where $\mathrm{mirrorCost}_i$ is the mirror cost (14) and $c_i(F_i;0,s,S)$ (`ssAvgCost`) is the long-run average holding and backlog cost of the $(s,S)$ policy. The long-run depletion of the width-$w$ cycle retains the lowest fraction $t$ of the probability mass of the width-$\hat w$ depletion, so these are the inequalities (D.2) and the outer inequality of (D.3).
-- source:
--   M. Hu, "A 5/2 Guarantee for Echelon Stock (s,S) Policies in One-Warehouse Multi-Retailer Systems", working paper (manuscript of November 2026), Appendix D, Lemma D.1 (Convex-Quantile Contraction), (D.2) and (D.3), p. E.25, proved in Appendix D.1, pp. E.27-E.28; applied in Step 2 of the proof of Theorem D.1, p. E.26, including its footnote on the three cost terms.

import Definitions.Def_owmr_renewal

open MeasureTheory
open scoped ENNReal NNReal

namespace OWMR
theorem dfr_window_contraction {n : ℕ} (N : Network n) (hN : N.Standing) (i : Fin n)
    (wh w t : ℝ) (hw : 0 < w) (hwwh : w ≤ wh) (ht0 : 0 < t) (ht1 : t ≤ 1)
    (hM : renewalM (N.marginal i) w = ENNReal.ofReal t * renewalM (N.marginal i) wh)
    (hconc : ConcaveOn ℝ (Set.Icc 0 wh)
      (fun x => (renewalMeasure (N.marginal i) (Set.Icc 0 x)).toReal)) :
    (∀ S Sh : ℝ, mirrorCost (N.marginal i) N.h N.p (S - w) S
        ≤ ENNReal.ofReal t * mirrorCost (N.marginal i) N.h N.p (Sh - wh) Sh) ∧
    ∀ Sh : ℝ, ∃ S : ℝ, ssAvgCost (N.marginal i) (N.F i) 0 (S - w) S
        ≤ ssAvgCost (N.marginal i) (N.F i) 0 (Sh - wh) Sh := by sorry
end OWMR
