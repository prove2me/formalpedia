-- Prove2me | Theorems.Thm_LogSupermodularBIS_Main_theorem_5_6
-- name    : LogSupermodularBIS.Main.theorem_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:34:31.433099+00:00
-- url     : https://prove2.me/theorems/7fe1a372-8079-4f77-ba35-9d41d929fc0a
-- title:
--   Theorem 5.6 — energy identity for smoothed threshold trees
-- statement:
--   Let $0<w\le1/2$, let $T$ be an ordered threshold tree on $d$ coordinates (thresholds in $[0,1]$, arbitrary real outputs), and let $g_T$ be its smoothing. Then
--   $$\sum_{S\subseteq[d]}\Bigl(1-\frac w2\Bigr)^{-|S|}\|(g_T)_S\|_2^2=\|T\|_2^2.\tag{5.5}$$
--   Consequently $\sum_{S\ne\emptyset}(1-w/2)^{-|S|}\|(g_T)_S\|_2^2=\mathrm{Var}(T)$, and for every integer $D\ge0$,
--   $$\|\Pi_{>D}g_T\|_2^2\le\Bigl(1-\frac w2\Bigr)^{D+1}\mathrm{Var}(T).\tag{5.6}$$
--
--   Differences from the source: none.
-- source:
--   Jingcheng Liu, Yitong Yin, STOC 2027 submission #1385 (October 2026), p. 27 (PDF 28), Theorem 5.6, (5.5), (5.6)

import Definitions.Def_LogSupermodularBIS_Main_Smoothing

open MeasureTheory

set_option autoImplicit false

namespace LogSupermodularBIS.Main

/-- Theorem 5.6 (Energy identity), p. 27, with squared `L²` norms. -/
theorem theorem_5_6 {d : ℕ} (w : ℝ) (hw : w ∈ Set.Ioc (0 : ℝ) (1 / 2)) (T : ThresholdTree d)
    (hT : T.Valid) :
    (∑ S : Finset (Fin d), ((1 - w / 2) ^ S.card)⁻¹ *
        l2Norm (hoeffdingComponent S (T.smoothing w)) ^ 2) = l2Norm T.eval ^ 2 ∧
    (∑ S ∈ (Finset.univ : Finset (Finset (Fin d))).filter (fun S => S.Nonempty),
        ((1 - w / 2) ^ S.card)⁻¹ * l2Norm (hoeffdingComponent S (T.smoothing w)) ^ 2) =
      variance T.eval ∧
    ∀ D : ℕ, l2Norm (highDegreeTail D (T.smoothing w)) ^ 2 ≤
      (1 - w / 2) ^ (D + 1) * variance T.eval := by sorry

end LogSupermodularBIS.Main
