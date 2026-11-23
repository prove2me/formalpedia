-- Prove2me | Theorems.Thm_MultiwayGap2325_Main_Supplement_computer_aided_flow_instance
-- name    : MultiwayGap2325.Main.Supplement.computer_aided_flow_instance
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-23T04:00:12.666932+00:00
-- url     : https://prove2.me/theorems/fb70a4d2-36be-4415-917f-36481eb8f7a6
-- title:
--   Proposition 3.6 — The rounded $q=11$ flow certificate
-- statement:
--   There is a valid flow instance $D$ on $\Delta_{11}$ with threshold $T=249/400$ whose fractional cost $L>0$ and exact value are
--   $$
--   \frac{B-R}{L}=\beta=\frac{159389999561650025}{129321858575204877},
--   $$
--   where $B$ is its total terminal-edge mass and $R$ its total conservation allowance.
--
--   This is Proposition 3.6, proved in §7.6 from the rounded integer table using $q=11$, $n=3$, $r_0=5$, and common denominator $230000000000$. The table satisfies the boundary and integer-capacity checks of Proposition 7.5; equations (37)–(39) give $B=1725000000167/1725000000000$, $R=2593033/910800000000000$, and $L=43107286191734959/53130000000000000$.
--
--   **Formalization Note** The statement asserts the actual `IsFlowInstance` predicate for the full cellwise geometric flow data. The scalar arithmetic alone does not prove this existence claim; the finite certificate and its soundness are required.
-- source:
--   Dimitar Chakarov and Yury Makarychev, STOC 2027 submission #697, Proposition 3.6 and its proof in §7.6, especially equation (39), p.31; certificate availability p.32.

import Definitions.Def_MultiwayGap2325_Main_Supplement_Flows

open MeasureTheory MultiwayGap2325.Main MultiwayGap2325.Main.Supplement

/-- Proposition 3.6, §7.6 p.31: the rounded integer table determines a valid
flow instance on the eleven-vertex simplex with the exact displayed value. -/
theorem MultiwayGap2325.Main.Supplement.computer_aided_flow_instance :
    ∃ D : FlowData 11, IsFlowInstance (249 / 400 : ℝ) D ∧
      0 < totalL (249 / 400 : ℝ) D.weighting ∧
      (totalB (249 / 400 : ℝ) D.weighting - totalR (249 / 400 : ℝ) D) /
        totalL (249 / 400 : ℝ) D.weighting = MultiwayGap2325.Main.beta := by sorry
