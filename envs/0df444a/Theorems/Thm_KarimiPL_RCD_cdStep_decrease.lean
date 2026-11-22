-- Prove2me | Theorems.Thm_KarimiPL_RCD_cdStep_decrease
-- name    : KarimiPL.RCD.cdStep_decrease
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-09T02:35:59.141399+00:00
-- url     : https://prove2.me/theorems/1c742fa1-8b2d-424b-82f7-3bc7e319ccef
-- title:
--   Proof of Theorem 3, p. 5 — one coordinate step decreases f
-- statement:
--   Let $d\ge1$. Suppose $f:\mathbb R^d\to\mathbb R$ obeys the coordinate-wise upper bound (5) with $L>0$. For any point $x$ and coordinate $i$, take the step $T_i(x)=x-L^{-1}\nabla_i f(x)e_i$. Then
--
--   $$
--   f(T_i(x))\le f(x)-\frac1{2L}|\nabla_i f(x)|^2.
--   $$
--
--   This is the one-coordinate decrease stated at the start of the proof of Theorem 3. It applies to every chosen coordinate, before averaging over random choices.
-- source:
--   Karimi, Nutini, Schmidt, arXiv:1608.04636v4, proof of Theorem 3, first displayed inequality, p. 5

import Mathlib
import Definitions.Def_KarimiPL_RCD_Setting

namespace KarimiPL.RCD

/-- First displayed inequality in the proof of Theorem 3, p. 5. -/
theorem cdStep_decrease {d : ℕ} (hd : 0 < d) (f : KarimiPL.Rel.E d → ℝ) (L : ℝ)
    (hL : 0 < L) (hcoord : CoordLipschitz f L) :
    ∀ (x : KarimiPL.Rel.E d) (i : Fin d),
      f (cdStep f L x i) ≤ f x - 1 / (2 * L) * (gradient f x i) ^ 2 := by sorry

end KarimiPL.RCD
