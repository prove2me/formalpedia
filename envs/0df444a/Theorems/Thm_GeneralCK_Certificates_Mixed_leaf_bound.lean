-- Prove2me | Theorems.Thm_GeneralCK_Certificates_Mixed_leaf_bound
-- name    : GeneralCK.Certificates.Mixed.leaf_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-24T21:06:44.387988+00:00
-- url     : https://prove2.me/theorems/f7673ae4-d2e5-40fc-9c86-74f9692b5c77
-- title:
--   Interval criterion bounding the compact mixed profile by thirteen sixths
-- statement:
--   Let $l,u,a,b,c,d,v$ be real numbers with $0<l\le v\le u<1/2$. Suppose $a\ge-\log l$, $b\ge-\log(1-u)$, $c\le-\log u$, $d\le-\log(1-l)$, $(c+d)/2>0$, and $a+b-(1-2u)^2\ge0$. If $$2(1-2l)(ua+(1-l)b)^2\bigl(a+b-(1-2u)^2\bigr)\le\frac{13}{6}\frac{69314718}{100000000}\bigl(4l(1-u)\bigr)^2\left(\frac{c+d}{2}\right)^3,$$ then the mixed profile $P$ defined by the accompanying natural-entropy formulas satisfies $$P(v)\le13/6.$$ The endpoint logarithm bounds and a rational numerical comparison thus certify an entire interval, rather than individual sample points.
-- source:
--   https://github.com/dpwoodru/general-courtade-kumar-lean/blob/04b6fc3f75b10c3c43702a883ddf888b0608a9a0/browse/GeneralCK/Certificates/MixedBounds.lean#L26-L97

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_GeneralCK_MixedBounds

open GeneralCK GeneralCK.Certificates GeneralCK.Certificates.Mixed

set_option maxHeartbeats 800000 in

theorem GeneralCK.Certificates.Mixed.leaf_bound {l u a b c d v : ℝ}
    (hl : 0 < l) (hlu : l ≤ u) (hu : u < 1/2)
    (hv₀ : l ≤ v) (hv₁ : v ≤ u)
    (ha : -Real.log l ≤ a) (hb : -Real.log (1-u) ≤ b)
    (hc : c ≤ -Real.log u) (hd : d ≤ -Real.log (1-l))
    (hcpos : 0 < (c+d)/2)
    (hnumpos : 0 ≤ a+b-(1-2*u)^2)
    (hnumeric :
      2*(1-2*l)*(u*a+(1-l)*b)^2*(a+b-(1-2*u)^2) ≤
        (13/6)*((69314718/100000000 : ℝ)*(4*l*(1-u))^2*((c+d)/2)^3)) :
    profile v ≤ 13/6 := by sorry
