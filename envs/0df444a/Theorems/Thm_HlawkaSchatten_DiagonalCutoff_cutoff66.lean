-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff_cutoff66
-- name    : HlawkaSchatten.DiagonalCutoff.cutoff66
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-10T05:21:56.584862+00:00
-- url     : https://prove2.me/theorems/859386f5-5eed-4cd7-b46c-0dc73571d372
-- title:
--   The least uniform complex coordinate Hlawka constant for $p \ge 66$
-- statement:
--   For every real exponent $p\ge 66$, let $N_p(x)$ be the foundation's finite coordinate $p$-norm and let $K_p$ be its unchanged cyclic constant, the supremum of the cyclic ratio over $t\in[1/2,2]$.
--
--   Then $K_p$ is the least real constant $C$ such that the triple deficit $N_p(x)+N_p(y)+N_p(z)-N_p(x+y+z)$ is at most $C$ times the pair-deficit sum $2(N_p(x)+N_p(y)+N_p(z))-N_p(x+y)-N_p(x+z)-N_p(y+z)$, for every natural-number dimension $n$ and all complex vectors $x,y,z$ in that dimension.
--
--   This combines admissibility and optimality uniformly over all finite complex coordinate dimensions, including dimension zero and triples with unequal or zero norms. The accepted cutoff-$70$ theorem covers every $p\ge 70$. This statement is the same leastness claim from $66$ upward.
--
--   **Formalization Note.** The statement is `IsLeast` of the set of uniform complex `HasHlawkaConstant` bounds, with least element `cyclicConstant p`.
-- source:
--   https://prove2.me/campaigns/sharp-diagonal-hlawka-constant

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sign.Basic
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Module
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.Order.Compact

/-! # The least dimension-independent complex coordinate Hlawka constant

This packages admissibility and the three-coordinate cyclic obstruction into
one statement, with an explicit lower cutoff on the real exponent.
-/

open HlawkaSchatten
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalCutoff.cutoff66 :
    ∀ p : ℝ, 66 ≤ p →
      IsLeast {C : ℝ | ∀ n : ℕ,
        HasHlawkaConstant (lpNorm p : (Fin n → ℂ) → ℝ) C}
        (cyclicConstant p) := by sorry
