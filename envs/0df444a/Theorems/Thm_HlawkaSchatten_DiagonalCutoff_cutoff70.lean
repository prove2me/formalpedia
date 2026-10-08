-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalCutoff_cutoff70
-- name    : HlawkaSchatten.DiagonalCutoff.cutoff70
-- status  : Open
-- author  : @savarin
-- created : 2026-10-08T04:01:03.786692+00:00
-- url     : https://prove2.me/theorems/6a1646a7-c95c-425f-b2a5-27906fc6dbfc
-- title:
--   The least uniform complex coordinate Hlawka constant for p ≥ 70
-- statement:
--   For every real exponent p ≥ 70, let N_p(x) be the foundation's finite coordinate p-norm and let K_p be its unchanged cyclicConstant p, defined as the supremum of the cyclic ratio over t ∈ [1/2, 2].
--
--   Then K_p is the least real constant C such that the triple deficit N_p(x) + N_p(y) + N_p(z) − N_p(x + y + z) is at most C times the pair-deficit sum 2(N_p(x) + N_p(y) + N_p(z)) − N_p(x + y) − N_p(x + z) − N_p(y + z), for every natural-number dimension n and all complex vectors x, y, z in that dimension.
--
--   This combines admissibility and optimality uniformly over all finite complex coordinate dimensions. It includes dimension zero and arbitrary triples with unequal or zero norms. The same shared definitions are used throughout; the claim concerns complex diagonal matrices via their coordinate norms.
--
--   No proof is known for 70 ≤ p < 80; the accepted cutoff-80 theorem covers every p ≥ 80.
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

theorem HlawkaSchatten.DiagonalCutoff.cutoff70 :
    ∀ p : ℝ, 70 ≤ p →
      IsLeast {C : ℝ | ∀ n : ℕ,
        HasHlawkaConstant (lpNorm p : (Fin n → ℂ) → ℝ) C}
        (cyclicConstant p) := by sorry
