-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_nonnegative_of_curvature_margins
-- name    : HlawkaSchatten.DiagonalCutoff16.nonnegative_of_curvature_margins
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-25T22:28:37.328259+00:00
-- url     : https://prove2.me/theorems/9ef05b46-cbaf-42f7-baf6-3547857047bb
-- title:
--   A quantitative curvature criterion for cyclic Hlawka nonnegativity
-- statement:
--   Let $p>4$, and let $K_p$ be the cyclic Hlawka constant, with $1/2\le K_p$ and $cp\le K_p\le p/2$. Consider triples $X=(X_0,X_1,X_2)$ whose diagonal coordinates lie in $[-u,-\ell]$ and off-diagonal coordinates in $[v,w]$, whose singleton norms are at most $U$, whose total norm is at most $A$, whose complementary-coordinate pair sums are at least $J$, and whose off-diagonal sum is at least $W_0$.
--   Choose positive $m,s,U,A,L,\varepsilon_1,\varepsilon_2$, with $M,\eta\ge0$, satisfying
--   $$m\le\ell,v,\quad u,w\le M,\quad s\le t,\quad L\le\max(2v,J),\quad s\le L-u,$$
--   $$\min(2w-\ell,A)\le t,\quad u-v\le\eta,\quad \min(w-\ell,A-v)\le\eta,\quad u\le2v,\quad4A\le W_0.$$
--   Define
--   $$F=\frac{s^2+t^2}{m^2(s+t)^2},\quad G_T=4M^2(1+\varepsilon_2)F(1+\varepsilon_1),$$
--   $$G_C=12M^2(1+\varepsilon_2)F(1+1/\varepsilon_1)+(7/4+2\eta/L)^2(1+1/\varepsilon_2).$$
--   If
--   $$\frac p2G_T\frac AL\left(\frac{\eta A}{Ls}\right)^{p-2}\le1,\qquad \frac{G_C}{2}\frac UL\left(\frac{\eta U}{Lm}\right)^{p-2}\le2c-\frac1p,$$
--   then the original Hlawka deficit at $K_p$ is nonnegative for every such triple. The geometric bounds define a convex domain invariant under simultaneous row and column permutations. The criterion packages the Hessian and cyclic averaging argument used by the cutoff-16 interval certificates.
-- source:
--   Reusable parameterized analytic component of the cutoff-16 extension. The proof reuses attributed Apache-2.0 generic normalization, Hessian and averaging arguments of Ezzeri Esa, bwdaugherty and Yuxuan Xu from accepted Prove2Me submissions 4753aff4-c621-4df6-9535-63c865f87fd0 and de577b6b-0253-45ac-9b17-ccf002bb69a6. The formal statement exposes the parameters required for the new cutoff-16 numerical windows. Published separately to keep subsequent interval verification within the platform time limit.

import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Normalization
import Mathlib.Tactic.Abel
import Mathlib.Analysis.Convex.Function
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Normed.Module.Convex
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic.Ring
import Mathlib.Analysis.MeanInequalities
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Coordinates
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Mathlib.Tactic.FinCases
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_NormHessian
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxGeometry
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxCoordinates
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.GCongr
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxConvexity
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_BoxHessian
import Mathlib.Topology.Order.Compact
open HlawkaSchatten HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff16.nonnegative_of_curvature_margins
    {p c ell u v w U A J W0 m M L s t eta eps1 eps2 gT gC : ℝ}
    (hp : 4 < p) (hK : 1/2 ≤ cyclicConstant p)
    (hKlo : c*p ≤ cyclicConstant p) (hKhi : cyclicConstant p ≤ p/2)
    (hm : 0 < m) (hM : 0 ≤ M) (hs : 0 < s) (hst : s ≤ t)
    (hU : 0 < U) (hA : 0 < A) (hLpos : 0 < L) (heta : 0 ≤ eta)
    (heps1 : 0 < eps1) (heps2 : 0 < eps2)
    (hmell : m ≤ ell) (hmv : m ≤ v) (huM : u ≤ M) (hwM : w ≤ M)
    (hL : L ≤ max (2*v) J) (hsgeom : s ≤ L-u) (htgeom : min (2*w-ell) A ≤ t)
    (hetalo : u-v ≤ eta) (hetahi : min (w-ell) (A-v) ≤ eta)
    (huv : u ≤ 2*v) (hWA : 4*A ≤ W0)
    (hGT : gT = 4*M^2*(1+eps2)*((s^2+t^2)/(m^2*(s+t)^2))*(1+eps1))
    (hGC : gC = 12*M^2*(1+eps2)*((s^2+t^2)/(m^2*(s+t)^2))*(1+1/eps1) +
      (7/4+2*(eta/L))^2*(1+1/eps2))
    (hNT : (p/2)*gT*(A/L)*((eta*A)/(L*s))^(p-2) ≤ 1)
    (hNC : (gC/2)*(U/L)*((eta*U)/(L*m))^(p-2) ≤ 2*c-1/p)
    (X : Fin 3 → Fin 3 → ℝ)
    (hbox : ∀ j i, if j = i then -u ≤ X j i ∧ X j i ≤ -ell
      else v ≤ X j i ∧ X j i ≤ w)
    (hrows : ∀ i, lpNorm p (X i) ≤ U)
    (htotal : lpNorm p (X 0 + X 1 + X 2) ≤ A)
    (hpairs : ∀ i j k : Fin 3, i ≠ j → i ≠ k → j ≠ k → J ≤ X j i + X k i)
    (hoff : W0 ≤ X 0 1 + X 0 2 + X 1 0 + X 1 2 + X 2 0 + X 2 1) :
    0 ≤ tripleDeficit p (cyclicConstant p) X := by sorry
