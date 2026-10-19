-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalConstruction_campaign_cutoff21
-- name    : HlawkaSchatten.DiagonalConstruction.campaign_cutoff21
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-17T08:15:07.475682+00:00
-- url     : https://prove2.me/theorems/db286144-c8c4-4918-9bc9-03fcadedfffd
-- title:
--   The least uniform complex coordinate Hlawka constant for p ≥ 21
-- statement:
--   For every real exponent p ≥ 21, let N_p(x) be the foundation's finite coordinate p-norm and let K_p be its unchanged cyclicConstant p, defined as the supremum of the cyclic ratio over t ∈ [1/2, 2].
--
--   Then K_p is the least real constant C such that the triple deficit N_p(x) + N_p(y) + N_p(z) − N_p(x + y + z) is at most C times the pair-deficit sum 2(N_p(x) + N_p(y) + N_p(z)) − N_p(x + y) − N_p(x + z) − N_p(y + z), for every natural-number dimension n and all complex vectors x, y, z in that dimension.
--
--   This combines admissibility and optimality uniformly over all finite complex coordinate dimensions. It includes dimension zero and arbitrary triples with unequal or zero norms. The same shared definitions are used throughout; the claim concerns complex diagonal matrices via their coordinate norms.
-- source:
--   Yuxuan Xu (徐宇轩), School of Computer Science, Wuhan University. A computer-assisted sharp diagonal Hlawka inequality for real exponents p >= 21, v1, 17 October 2026. https://github.com/Anchen-AI4Math/hlawka-diagonal-certificates/blob/2f1ec21c8ce4e3d9de33f57119f73f8504de0bd3/paper/main.pdf . LaTeX: https://github.com/Anchen-AI4Math/hlawka-diagonal-certificates/blob/2f1ec21c8ce4e3d9de33f57119f73f8504de0bd3/paper/main.tex . Reproducibility: https://github.com/Anchen-AI4Math/hlawka-diagonal-certificates/blob/2f1ec21c8ce4e3d9de33f57119f73f8504de0bd3/results/release-replay.json . AI-assisted research preprint; independent analytic review pending; no new Lean proof. Main Theorem 1.1. The campaign template is preserved, changing only its declaration name and numeric cutoff.

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

theorem HlawkaSchatten.DiagonalConstruction.campaign_cutoff21 :
    ∀ p : ℝ, 21 ≤ p →
      IsLeast {C : ℝ | ∀ n : ℕ,
        HasHlawkaConstant (lpNorm p : (Fin n → ℂ) → ℝ) C}
        (cyclicConstant p) := by sorry
