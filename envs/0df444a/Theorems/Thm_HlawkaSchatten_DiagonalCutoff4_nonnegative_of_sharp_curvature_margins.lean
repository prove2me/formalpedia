-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff4_nonnegative_of_sharp_curvature_margins
-- name    : HlawkaSchatten.DiagonalCutoff4.nonnegative_of_sharp_curvature_margins
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-28T00:33:51.261695+00:00
-- url     : https://prove2.me/theorems/70c27596-6a39-4336-9595-0c5c0109ae6f
-- title:
--   Sharp-constant curvature and averaging criterion for every real p > 2
-- statement:
--   Let $p>2$, $K=K_p\ge1/2$, and $K_{\rm lo}\le K\le K_{\rm hi}$. Let $X$ be a real $3\times3$ matrix with
--   $$-u\le X_{ii}\le-\ell,\qquad v\le X_{ji}\le w\quad(j\ne i).$$
--   Assume its three row norms are at most $U$, its total-vector norm is at most $A$, each complementary pair has main coordinate at least $J$, and its six off-diagonal entries sum to at least $W_0$.
--   Choose $m,s,U,A,L,\epsilon_1,\epsilon_2>0$, $M,\eta\ge0$, and $t\ge s$ with
--   $$m\le\min(\ell,v),\quad\max(u,w)\le M,\quad L\le\max(2v,J),\quad s\le L-u,\quad\min(2w-\ell,A)\le t,$$
--   $$u-v\le\eta,\quad\min(w-\ell,A-v)\le\eta,\quad u\le2v,\quad w\le2\ell.$$
--   Define
--   $$g_T=4M^2(1+\epsilon_2)\frac{s^2+t^2}{m^2(s+t)^2}(1+\epsilon_1),$$
--   $$g_C=12M^2(1+\epsilon_2)\frac{s^2+t^2}{m^2(s+t)^2}(1+1/\epsilon_1)+(7/4+2\eta/L)^2(1+1/\epsilon_2).$$
--   If
--   $$K_{\rm hi}g_T\frac AL\left(\frac{\eta A}{Ls}\right)^{p-2}\le1,\qquad
--   K_{\rm hi}g_C\frac UL\left(\frac{\eta U}{Lm}\right)^{p-2}\le2K_{\rm lo}-1,$$
--   then $(2K-1)S+T-KP\ge0$, where $S$ is the sum of the row norms, $T$ the total-vector norm, and $P$ the sum of the three pair norms.
--   This is a sufficient local criterion. It does not assert that its hypotheses hold for every normalized counterexample.
-- source:
--   Sharp diagonal Hlawka campaign: https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Analytic strengthening of the proved cutoff-six method. Generic norm facts retain Apache-2.0 attribution to Ezzeri Esa, bwdaugherty and Yuxuan Xu.

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Normalization
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff4.nonnegative_of_sharp_curvature_margins
    {p Klo Khi ell u v w U A J W0 m M L s t eta eps1 eps2 gT gC : ℝ}
    (hp : 2 < p) (hK : 1/2 ≤ cyclicConstant p)
    (hKlo : Klo ≤ cyclicConstant p) (hKhi : cyclicConstant p ≤ Khi)
    (hm : 0 < m) (hM : 0 ≤ M) (hs : 0 < s) (hst : s ≤ t)
    (hU : 0 < U) (hA : 0 < A) (hLpos : 0 < L) (heta : 0 ≤ eta)
    (heps1 : 0 < eps1) (heps2 : 0 < eps2)
    (hmell : m ≤ ell) (hmv : m ≤ v) (huM : u ≤ M) (hwM : w ≤ M)
    (hL : L ≤ max (2*v) J) (hsgeom : s ≤ L-u) (htgeom : min (2*w-ell) A ≤ t)
    (hetalo : u-v ≤ eta) (hetahi : min (w-ell) (A-v) ≤ eta)
    (huv : u ≤ 2*v) (hWA : w ≤ 2*ell)
    (hGT : gT = 4*M^2*(1+eps2)*((s^2+t^2)/(m^2*(s+t)^2))*(1+eps1))
    (hGC : gC = 12*M^2*(1+eps2)*((s^2+t^2)/(m^2*(s+t)^2))*(1+1/eps1) +
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
