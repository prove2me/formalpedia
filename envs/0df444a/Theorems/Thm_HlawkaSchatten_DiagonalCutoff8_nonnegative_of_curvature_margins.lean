-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff8_nonnegative_of_curvature_margins
-- name    : HlawkaSchatten.DiagonalCutoff8.nonnegative_of_curvature_margins
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-27T15:07:05.88174+00:00
-- url     : https://prove2.me/theorems/54e271d7-5ac8-454d-98a8-40415880c0eb
-- title:
--   Hlawka convexity criterion with a coordinate-box orbit bound
-- statement:
--   For real exponents $p>4$, the diagonal Hlawka deficit with cyclic constant is nonnegative on a norm-capped coordinate box whenever the displayed two dimensionless Hessian bounds hold. Diagonal magnitudes lie between $\ell$ and $u$, off-diagonal entries between $v$ and $w$, with $0<v$, $u\le2v$ and $w\le2\ell$. These last bounds ensure that the simultaneous-permutation average has cyclic parameter in $[1/2,2]$. The remaining parameters bound row and total norms, principal pair coordinates, and transverse Hessian errors. This version supports localization below cutoff 12.
-- source:
--   Refinement of the proved curvature criterion in the sharp diagonal Hlawka campaign, https://prove2.me/campaigns/sharp-diagonal-hlawka-constant . Original Hessian and averaging proofs by Ezzeri Esa, bwdaugherty and Yuxuan Xu (Apache-2.0). The orbit-range hypothesis is replaced by a direct bound from the coordinate box.

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

theorem HlawkaSchatten.DiagonalCutoff8.nonnegative_of_curvature_margins
    {p c ell u v w U A J W0 m M L s t eta eps1 eps2 gT gC : ℝ}
    (hp : 4 < p) (hK : 1/2 ≤ cyclicConstant p)
    (hKlo : c*p ≤ cyclicConstant p) (hKhi : cyclicConstant p ≤ p/2)
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
