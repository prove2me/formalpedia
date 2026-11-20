-- Prove2me | Theorems.Thm_LL_DensitySlope517_leaf_two_variation_quadrature
-- name    : LL_DensitySlope517.leaf_two_variation_quadrature
-- status  : Proved
-- author  : @sthubbar
-- created : 2026-11-17T15:37:03.421051+00:00
-- url     : https://prove2.me/theorems/7552905e-4de5-4c6b-9ab6-a5841932cc66
-- title:
--   Quadrature bound for the variation majorant over E2
-- statement:
--   Let $\varepsilon$ be real with $0<\varepsilon\le10^{-8}$. Let $F(a,b)=1/\bigl(ab(99/100-a-b)(1-a-b)\bigr)$ if $a+3b\ge1$, $F(a,b)=(107/200)/(ab^3)$ if $99/100\le a+3b<1$, and $F(a,b)=(7/200)/(ab^3)$ if $a+3b<99/100$. Then the iterated interval integral $\int_{1/10}^{1/2}\int_{1/10}^{1/2}G(a,b)\,db\,da$ is at most $2$, where $G(a,b)=F(a,b)$ when $(a,b)$ lies in the set $E_2$ given by the predicate above with parameter $\varepsilon$, and $G(a,b)=0$ otherwise.
-- source:
--   Baker, Harman and Pintz 1997, Section 5, page 51, display 5.17; the explicit majorant of the variation of the $E_2$ integrand used to bound the slope of the lower density near $s=1$.

import Mathlib
import Definitions.Def_LL_DensitySlope517_lowerTwoDiscarded

open Classical

namespace LL_DensitySlope517
theorem leaf_two_variation_quadrature {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    (∫ a in (1/10:ℝ)..(1/2:ℝ), ∫ b in (1/10:ℝ)..(1/2:ℝ),
      (if lowerTwoDiscarded ε a b then
        (if 1 ≤ a+3*b then 1/(a*b*(99/100-a-b)*(1-a-b))
          else if 99/100 ≤ a+3*b then (107/200)/(a*b^3) else (7/200)/(a*b^3))
      else 0)) ≤ 2 := by sorry
end LL_DensitySlope517
