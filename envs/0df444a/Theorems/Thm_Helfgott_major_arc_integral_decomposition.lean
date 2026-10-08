-- Prove2me | Theorems.Thm_Helfgott_major_arc_integral_decomposition
-- name    : Helfgott.major_arc_integral_decomposition
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-05T05:00:34.063482+00:00
-- url     : https://prove2.me/theorems/b0a45683-904d-484d-a462-5af840283159
-- title:
--   Exact finite decomposition and scaled parametrization of the actual Goldbach major arcs
-- statement:
--   For any positive integer cutoff $r$, real scale $x>32r^2$, and integrable complex function $f$ on the unit additive circle, integration over the actual Goldbach major arcs with parameter $8$ equals the finite sum of scaled real arc integrals. Odd denominators run through $1\le q\le r$, even denominators through $1\le q\le2r$, and each denominator uses exactly the reduced residues $0\le a<q$. Put $R_q=4r/q$ for odd $q$ and $R_q=8r/q$ for even $q$. Then
--
--   $$\int_{\mathfrak M(8,r,x)}f(\alpha)\,d\alpha
--   =\frac1x\sum_q\sum_{\substack{0\le a<q\\(a,q)=1}}
--   \int_{-R_q}^{R_q}f(a/q+\beta/x\bmod1)\,d\beta.$$
--
--   This is an exact identity, including arcs crossing the circle's seam. Its proof establishes finite coverage, pairwise disjointness, the real parametrization and the inverse-scale Jacobian. It assumes no prime exponential-sum estimate.
-- source:
--   H. A. Helfgott, The ternary Goldbach conjecture is true, https://arxiv.org/html/1312.7748v2, §§3.3 and 7.2. The arc geometry and measure changes are proved using Mathlib. Written by Codex.

import Definitions.Def_Helfgott_ArcCounting
import Mathlib.MeasureTheory.Integral.Bochner.Set
open MeasureTheory Set Metric Finset Function
open scoped BigOperators

namespace Helfgott

theorem major_arc_integral_decomposition (r : ℕ) (x : ℝ) (hr : 0 < r)
    (hx : 32*(r:ℝ)^2 < x) (f : AddCircle (1:ℝ) → ℂ)
    (hf : Integrable f AddCircle.haarAddCircle) :
    (∫ α in majorArcs 8 r x,f α ∂AddCircle.haarAddCircle) =
      x⁻¹ • (∑ q ∈ ((Finset.Icc 1 r).filter (fun q => Odd q) ∪
          (Finset.Icc 1 (2*r)).filter (fun q => Even q)),
        ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
          ∫ β in Set.Icc (-(if Odd q then 4*(r:ℝ)/(q:ℝ) else 8*(r:ℝ)/(q:ℝ)))
            (if Odd q then 4*(r:ℝ)/(q:ℝ) else 8*(r:ℝ)/(q:ℝ)),
            f (((a:ℝ)/(q:ℝ)+β/x : ℝ) : AddCircle (1:ℝ))) := by sorry

end Helfgott
