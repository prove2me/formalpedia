-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalConstruction_campaign_cutoff2
-- name    : HlawkaSchatten.DiagonalConstruction.campaign_cutoff2
-- status  : Open
-- author  : @savarin
-- created : 2026-10-26T05:37:26.097115+00:00
-- url     : https://prove2.me/theorems/7fe6f02d-65e5-4c21-9796-c83889b29b9d
-- title:
--   The least uniform complex coordinate Hlawka constant for p ≥ 2
-- statement:
--   For every real exponent p ≥ 2, let N_p(x) be the foundation's finite coordinate p-norm and let K_p be its unchanged cyclicConstant p, defined as the supremum of the cyclic ratio over t ∈ [1/2, 2].
--
--   Then K_p is the least real constant C such that the triple deficit N_p(x) + N_p(y) + N_p(z) − N_p(x + y + z) is at most C times the pair-deficit sum 2(N_p(x) + N_p(y) + N_p(z)) − N_p(x + y) − N_p(x + z) − N_p(y + z), for every natural-number dimension n and all complex vectors x, y, z in that dimension.
--
--   This combines admissibility and optimality uniformly over all finite complex coordinate dimensions. It includes dimension zero and arbitrary triples with unequal or zero norms. The same shared definitions are used throughout; the claim concerns complex diagonal matrices via their coordinate norms.
--
--   No proof is known for 2 ≤ p < 16; the accepted cutoff-16 theorem covers every p ≥ 16. The original confinement method (exhausted at 62), the technique that reached 21, and the window-by-window proof that reached 16 are available as prior art. At p = 2 the constant C_p equals 1 exactly, reached at t = 2.
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

theorem HlawkaSchatten.DiagonalConstruction.campaign_cutoff2 :
    ∀ p : ℝ, 2 ≤ p →
      IsLeast {C : ℝ | ∀ n : ℕ,
        HasHlawkaConstant (lpNorm p : (Fin n → ℂ) → ℝ) C}
        (cyclicConstant p) := by sorry
