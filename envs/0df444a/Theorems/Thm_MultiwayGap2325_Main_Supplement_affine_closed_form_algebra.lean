-- Prove2me | Theorems.Thm_MultiwayGap2325_Main_Supplement_affine_closed_form_algebra
-- name    : MultiwayGap2325.Main.Supplement.affine_closed_form_algebra
-- status  : Open
-- author  : @Mr Robbins
-- created : 2026-11-22T23:04:24.136054+00:00
-- url     : https://prove2.me/theorems/ace1715f-d414-4f7a-9025-a00606d17527
-- title:
--   Telescoping and closed-form algebra for the affine constants
-- statement:
--   For $q\ge2$, $T\in(1/2,1)$, and $z=(1-T)/T$, the finite sums in equation (25) satisfy
--
--   $$
--   \sum_{r=2}^{q}\frac{(rT-1)z^{r-2}}{(r-1)!}=T\left(1-\frac{z^{q-1}}{(q-1)!}\right)
--   $$
--
--   and
--
--   $$
--   T\left(1-\frac{z^{q-1}}{(q-1)!}\right)-\frac{1-q(1-T)^{q-1}}{q!\,T^{q-2}}=T-\frac1{q!\,T^{q-2}}.
--   $$
--
--   Indeed, the $r$th term in the first sum is $Tz^{r-2}/(r-2)!-z^{r-1}/(r-1)!$, so the sum telescopes; the second identity follows from $z=(1-T)/T$ and $q!=q(q-1)!$.
--
--   **Formalization Note** This child contains only exact real-algebraic relations among the named closed forms and no geometric integral assertion.
-- source:
--   Dimitar Chakarov, Yury Makarychev, STOC 2027 submission #697 (October 2026), final telescoping sentence in the proof of Theorem 6.1 and equation (25), p.24.

import Definitions.Def_MultiwayGap2325_Main_Supplement_AffineData

namespace MultiwayGap2325.Main.Supplement

/-- Theorem 6.1, p.24: telescoping of B and the resulting closed form for B-R. -/
theorem affine_closed_form_algebra (q : ℕ) (hq : 2 ≤ q) (T : ℝ)
    (hT0 : 1 / 2 < T) (hT1 : T < 1) :
    affineBSum q T = affineBClosed q T ∧
      affineBClosed q T - affineRClosed q T = affineNetClosed q T := by sorry
