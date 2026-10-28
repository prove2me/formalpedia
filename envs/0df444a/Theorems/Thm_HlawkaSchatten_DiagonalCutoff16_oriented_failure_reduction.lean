-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff16_oriented_failure_reduction
-- name    : HlawkaSchatten.DiagonalCutoff16.oriented_failure_reduction
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-25T22:28:19.73564+00:00
-- url     : https://prove2.me/theorems/316a8cf7-462d-4995-870f-5f0c907271a6
-- title:
--   Parametric orientation reduction for Hlawka counterexamples
-- statement:
--   Write $K_p$ for the cyclic Hlawka constant and $\Delta_p(x,y,z)=K_p(2S-P)-(S-T)$ for the Hlawka deficit, where $S$ is the sum of the three singleton norms, $P$ is the sum of the three pair norms, and $T$ is the total norm. Let $p\ge\alpha>1$, $c>0$, $c\alpha>1$, $cp<K_p$, and $0<q<1$. Put
--   $$E_p(q)=\frac{1-q}{2\left(1-((1+q^p)/2)^{1/p}\right)}.$$
--   Assume $E_p(q)<K_p$ and choose $E,g$ such that
--   $$\frac{1099}{1000\alpha}6q\le E,\qquad \frac{2}{c\alpha}\le g,\qquad g+E<3-6q,\qquad 3q\le3-2(g+E).$$
--   If a real three-dimensional triple has negative deficit, there is a signed and permuted normalized triple $X=(X_0,X_1,X_2)$ with negative deficit and
--   $$\sum_i\|X_i\|_p=3,\qquad \|X_i\|_p\le T,\qquad 1\le T<3q.$$
--   The three pair norms differ from their complementary-coordinate sums by at most $E$, and
--   $$T-c\alpha P\le3-6c\alpha.$$
--   This parameterized reduction supplies the common normalized input to the finite interval localization proofs. It does not assert the final cutoff-16 inequality.
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

theorem HlawkaSchatten.DiagonalCutoff16.oriented_failure_reduction
    {p α c q E g : ℝ}
    (hα : 1 < α) (hαp : α ≤ p) (hc : 0 < c) (hcα : 1 < c*α)
    (hlinear : c*p < cyclicConstant p) (hq0 : 0 < q) (hq1 : q < 1)
    (henvelope : scalarEnvelope p q < cyclicConstant p)
    (hBE : (1099 / (1000 * α)) * (6*q) ≤ E)
    (hgap : 2/(c*α) ≤ g) (hsep : g+E < 3-6*q) (hTsep : 3*q ≤ 3-2*(g+E))
    (x y z : Fin 3 → ℝ) (hf : hlawkaDeficit p (cyclicConstant p) x y z < 0) :
    ∃ X : Fin 3 → Fin 3 → ℝ,
      (lpNorm p (X 0) + lpNorm p (X 1) + lpNorm p (X 2) = 3) ∧
      (∀ i, lpNorm p (X i) ≤ lpNorm p (X 0 + X 1 + X 2)) ∧
      (1 ≤ lpNorm p (X 0 + X 1 + X 2)) ∧
      (lpNorm p (X 0 + X 1 + X 2) < 3*q) ∧
      (lpNorm p (X 1 + X 2) - (X 1 0 + X 2 0) ≤ E) ∧
      (lpNorm p (X 0 + X 2) - (X 0 1 + X 2 1) ≤ E) ∧
      (lpNorm p (X 0 + X 1) - (X 0 2 + X 1 2) ≤ E) ∧
      (lpNorm p (X 0 + X 1 + X 2) - (c*α) *
        (lpNorm p (X 1 + X 2) + lpNorm p (X 0 + X 2) + lpNorm p (X 0 + X 1)) ≤ 3 - 6*(c*α)) ∧
      tripleDeficit p (cyclicConstant p) X < 0 := by sorry
