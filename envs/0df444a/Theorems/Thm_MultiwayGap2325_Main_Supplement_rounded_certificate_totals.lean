-- Prove2me | Theorems.Thm_MultiwayGap2325_Main_Supplement_rounded_certificate_totals
-- name    : MultiwayGap2325.Main.Supplement.rounded_certificate_totals
-- status  : Proved
-- author  : @Mr Robbins
-- created : 2026-11-23T03:34:24.862285+00:00
-- url     : https://prove2.me/theorems/971feb63-dac4-4cd4-b79e-c714375175d9
-- title:
--   Exact scalar totals of the Proposition 3.6 table
-- statement:
--   The totals displayed for the rounded $q=11$ certificate in equation (39), namely
--   $$
--   B=\frac{1725000000167}{1725000000000},\qquad
--   R=\frac{2593033}{910800000000000},\qquad
--   L=\frac{43107286191734959}{53130000000000000},
--   $$
--   satisfy $L>0$ and the exact identity
--   $$
--   \frac{B-R}{L}=\frac{159389999561650025}{129321858575204877}=\beta.
--   $$
--   This is the printed scalar arithmetic of §7.6. It does not assert the existence of the external tables $H,Z,W$, nor any of their geometric flow or capacity properties.
-- source:
--   Dimitar Chakarov and Yury Makarychev, STOC 2027 submission #697, Proposition 3.6, §7.6, equation (39), p.31.

import Definitions.Def_MultiwayGap2325_Main_RandomCuts

/-- The scalar totals printed in equation (39) for the external rounded table. -/
theorem MultiwayGap2325.Main.Supplement.rounded_certificate_totals :
    let B : ℝ := (1725000000167 : ℝ) / 1725000000000
    let R : ℝ := (2593033 : ℝ) / 910800000000000
    let L : ℝ := (43107286191734959 : ℝ) / 53130000000000000
    0 < L ∧ (B - R) / L = MultiwayGap2325.Main.beta := by sorry
