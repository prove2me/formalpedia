-- Prove2me | Theorems.Thm_FourBlockIP350_Main_Supplement_two_point_majorization
-- name    : FourBlockIP350.Main.Supplement.two_point_majorization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T18:07:59.002207+00:00
-- url     : https://prove2.me/theorems/43503ba0-4595-4fbf-81ff-11586983fb48
-- title:
--   Lemma B.4 — Two-point inequality for a convex function
-- statement:
--   Let $\phi:\mathbb R\to\mathbb R$ be convex. Suppose $a,b,c,d\in\mathbb R$ satisfy
--   $$a+b=c+d,\qquad \min\{a,b\}\le c,d\le\max\{a,b\}.$$
--   Then
--   $$\phi(c)+\phi(d)\le\phi(a)+\phi(b).$$
--
--   The paper cites this as Theorem 1 of Kadelburg, Đukić, Lukić and Matić (2005). It is applied coordinatewise, to the component functions of the objective and to $t\mapsto|t|$, in the proof of Lemma B.5.
--
--   Differences from the source: none.
-- source:
--   Klaus Jansen, Felix Ohnesorge, Corinna Wambsganz, A Fixed-Parameter Algorithm for 4-Block Integer Programming, STOC 2027 submission #350 (October 2026), p. 24, Lemma B.4 (Theorem 1 of [KÐLM05])

import Mathlib

namespace FourBlockIP350.Main.Supplement

/-- Lemma B.4 (Theorem 1 of [KÐLM05]), p. 24. -/
theorem two_point_majorization (ϕ : ℝ → ℝ) (hϕ : ConvexOn ℝ Set.univ ϕ)
    (a b c d : ℝ) (hsum : a + b = c + d)
    (hc : min a b ≤ c ∧ c ≤ max a b) (hd : min a b ≤ d ∧ d ≤ max a b) :
    ϕ c + ϕ d ≤ ϕ a + ϕ b := by sorry

end FourBlockIP350.Main.Supplement
