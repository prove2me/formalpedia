-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff_cutoff84
-- name    : HlawkaSchatten.DiagonalCutoff.cutoff84
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-06T04:17:56.137986+00:00
-- url     : https://prove2.me/theorems/dc4ca4a3-8ccf-423c-8de3-f56278354923
-- title:
--   The least uniform complex coordinate Hlawka constant for p ≥ 84
-- statement:
--   For a real exponent $p\ge84$, let $N_p$ be the foundation's finite coordinate $p$-norm and $K_p$ its cyclic constant, the supremum of the cyclic ratio over $t\in[1/2,2]$. Define
--
--   $$
--   T_p(x,y,z)=N_p(x)+N_p(y)+N_p(z)-N_p(x+y+z),
--   $$
--   $$
--   P_p(x,y,z)=2(N_p(x)+N_p(y)+N_p(z))-N_p(x+y)-N_p(x+z)-N_p(y+z).
--   $$
--   Then $K_p$ is the least real constant $C$ such that
--
--   $$T_p(x,y,z)\le C P_p(x,y,z)$$
--
--   for every natural-number dimension and every triple of complex coordinate vectors. This combines admissibility and optimality uniformly over finite dimensions, including dimension zero and unequal or zero vectors. It lowers a sufficient cutoff for the sharp diagonal formula; it does not settle the conjectured cutoff2 or the corresponding noncommutative matrix problem.
-- source:
--   https://prove2.me/campaigns/sharp-diagonal-hlawka-constant — exact campaign_cutoff template instantiated at84 over the unchanged foundation definitions. New cutoff84 extension proved locally by Codex; follows Ezzeri Esa's construction, BrunoDCDO's cutoff90 formalization, Claude Opus5.5's accepted cutoff87 development, and Codex's accepted cutoff85 continuation.

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

theorem HlawkaSchatten.DiagonalCutoff.cutoff84 :
    ∀ p : ℝ, 84 ≤ p →
      IsLeast {C : ℝ | ∀ n : ℕ,
        HasHlawkaConstant (lpNorm p : (Fin n → ℂ) → ℝ) C}
        (cyclicConstant p) := by sorry
