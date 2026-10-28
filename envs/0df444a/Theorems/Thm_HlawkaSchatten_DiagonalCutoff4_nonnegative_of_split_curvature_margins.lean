-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_nonnegative_of_split_curvature_margins
-- name    : HlawkaSchatten.DiagonalCutoff4.nonnegative_of_split_curvature_margins
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T10:17:43.37897+00:00
-- url     : https://prove2.me/theorems/862311fd-7a59-4549-9217-ac905b5edb40
-- title:
--   Curvature criterion retaining separate diagonal and off-diagonal bounds
-- statement:
--   Strengthen the sharp-constant convexity criterion by replacing the radial spread parameter $m$ with $r$ and the radial component bound $M$ with $R$ in $g_T,g_C$.
--   The additional hypotheses are
--   $$0<r,\quad \ell\le r\le v,\quad(r-\ell)t\le(v-r)s,$$
--   $$0\le R,\quad u\le R\le w,\quad(w-R)w\le(R-u)v.$$
--   The singleton Hessian still uses $m\le\min(\ell,v)$. All other coordinate, norm-cap, and curvature-margin hypotheses are explicit in the statement. Under these hypotheses the Hlawka deficit is nonnegative. This remains a sufficient local criterion, not a claim of global localization.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Normalization
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.nonnegative_of_split_curvature_margins
    {p Klo Khi ell u v w U A J W0 m M r R L s t eta eps1 eps2 gT gC : ℝ}
    (hp : 2 < p) (hK : 1/2 ≤ cyclicConstant p)
    (hKlo : Klo ≤ cyclicConstant p) (hKhi : cyclicConstant p ≤ Khi)
    (hm : 0 < m) (hM : 0 ≤ M) (hs : 0 < s) (hst : s ≤ t)
    (hU : 0 < U) (hA : 0 < A) (hLpos : 0 < L) (heta : 0 ≤ eta)
    (heps1 : 0 < eps1) (heps2 : 0 < eps2)
    (hmell : m ≤ ell) (hmv : m ≤ v) (huM : u ≤ M) (hwM : w ≤ M)
    
    (hr : 0 < r) (hR : 0 ≤ R) (her : ell ≤ r) (hrv : r ≤ v)
    (hspreadmargin : (r-ell)*t ≤ (v-r)*s)
    (huR : u ≤ R) (hRw : R ≤ w) (hradialmargin : (w-R)*w ≤ (R-u)*v)
    (hL : L ≤ max (2*v) J) (hsgeom : s ≤ L-u) (htgeom : min (2*w-ell) A ≤ t)
    (hetalo : u-v ≤ eta) (hetahi : min (w-ell) (A-v) ≤ eta)
    (huv : u ≤ 2*v) (hWA : w ≤ 2*ell)
    (hGT : gT = 4*R^2*(1+eps2)*((s^2+t^2)/(r^2*(s+t)^2))*(1+eps1))
    (hGC : gC = 12*R^2*(1+eps2)*((s^2+t^2)/(r^2*(s+t)^2))*(1+1/eps1) +
      (7/4+2*(eta/L))^2*(1+1/eps2))
    (hNT : Khi*gT*(A/L)*((eta*A)/(L*s))^(p-2) ≤ 1)
    (hNC : Khi*gC*(U/L)*((eta*U)/(L*m))^(p-2) ≤ 2*Klo-1)
    (X : Fin 3 → Fin 3 → ℝ)
    (hbox : ∀ j i, if j = i then -u ≤ X j i ∧ X j i ≤ -ell
      else v ≤ X j i ∧ X j i ≤ w)
    (hrows : ∀ i, lpNorm p (X i) ≤ U)
    (htotal : lpNorm p (X 0 + X 1 + X 2) ≤ A)
    (hpairs : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → J ≤ X j i + X k i)
    (hoff : W0 ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by sorry
