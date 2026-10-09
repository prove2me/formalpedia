-- Prove2me | Theorems.Thm_LearnNoConc_ERM_shift_starShaped
-- name    : LearnNoConc.ERM.shift_starShaped
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T00:48:10.26599+00:00
-- url     : https://prove2.me/theorems/435e3d5b-c980-4898-882d-e2219c6ea0bd
-- title:
--   Proof of Theorem 5.3, p. 23 — F convex, f* ∈ F ⇒ F − f* is star-shaped around 0
-- statement:
--   Let $F$ be a convex class of real functions on a set $\Omega$ and $f^*\in F$. Then the shifted class $F-f^*=\{f-f^*:f\in F\}$ is star-shaped around $0$: for every $f\in F$ and $0<\lambda\le1$,
--
--   $$\lambda(f-f^*)\in F-f^*.$$
--
--   This is what allows Corollary 5.5 to be applied to $H=F-f^*$ in the proof of Theorem 5.3.
-- source:
--   Mendelson, Learning without Concentration, arXiv:1401.0304v2, proof of Theorem 5.3, p. 23

import Mathlib
import Definitions.Def_LearnNoConc_ERM_Setting

namespace LearnNoConc.ERM

open MeasureTheory
open scoped ENNReal

/-- Proof of Theorem 5.3, p. 23: if `F` is convex and `f* ∈ F`, then `F − f*` is star-shaped
around `0`. -/
theorem shift_starShaped {Ω : Type*} (F : Set (Ω → ℝ)) (hFconv : Convex ℝ F)
    (fstar : Ω → ℝ) (hfstar : fstar ∈ F) :
    StarShaped (shift F fstar) := by sorry

end LearnNoConc.ERM
