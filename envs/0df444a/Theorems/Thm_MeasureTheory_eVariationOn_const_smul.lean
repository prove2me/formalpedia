-- Prove2me | Theorems.Thm_MeasureTheory_eVariationOn_const_smul
-- name    : MeasureTheory.eVariationOn_const_smul
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-31T07:34:57.596717+00:00
-- url     : https://prove2.me/theorems/494516dc-5e95-494f-9daf-23ea336e5556
-- title:
--   The variation of a curve scales under a dilation of the target
-- statement:
--   For a real scalar $c$ and a curve $f$ into a normed space,
--   $$V_s(c\,f)=|c|\,V_s(f).$$
--   Scaling a curve scales its length by the same factor.
--
--   **Role.** A great circle of radius $L$ is $L$ times the unit great circle, so its length over a parameter interval is $L$ times the length of the unit one. Together with the invariance of the variation under an isometry of the target and under a monotone reparametrisation, this is what turns the abstract statement "a great circle is parametrised by arclength" into the concrete value $2\pi\alpha L$ for the length of the image of a circle under a homogeneous harmonic map.
--
--   **The argument.** The variation is a supremum of sums of distances between consecutive values, and $d(cx,cy)=|c|\,d(x,y)$; the constant $|c|$ therefore factors out of each sum and, being a fixed element of $[0,\infty]$, out of the supremum.
-- source:
--   Standard; the behaviour of the length of a curve under a homothety of the target, used for the great circle of radius L in C. Breiner and B. K. Dees, arXiv:2604.16608, Lemma 3.2.

import Mathlib

namespace MeasureTheory

universe u v

theorem eVariationOn_const_smul {α : Type u} [LinearOrder α] {E : Type v}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (c : ℝ) (f : α → E) (s : Set α) :
    eVariationOn (fun x => c • f x) s
      = ENNReal.ofReal |c| * eVariationOn f s := by sorry

end MeasureTheory
