-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalConstruction_antitoneOn_scalarEnvelope
-- name    : HlawkaSchatten.DiagonalConstruction.antitoneOn_scalarEnvelope
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-28T17:14:27.604562+00:00
-- url     : https://prove2.me/theorems/d21550a7-d4a9-4c6f-8a28-1318f5b65795
-- title:
--   Monotonicity of the scalar envelope
-- statement:
--   For a real exponent $p\ge1$ and $q\in[0,1)$, define the scalar envelope root
--   $$
--   \rho_p(q) = \Bigl(\tfrac{1+q^p}{2}\Bigr)^{1/p}
--   $$
--   and the scalar envelope
--   $$
--   f_p(q) \;=\; \frac{1-q}{2\bigl(1-\rho_p(q)\bigr)}.
--   $$
--
--   The theorem states that $f_p$ is antitone (order-reversing, i.e. non-increasing) on the half-open interval $[0,1)$: for $0\le r\le q<1$,
--   $$
--   f_p(q) \;\le\; f_p(r).
--   $$
--
--   Elsewhere in the diagonal construction, $f_p$ evaluated at $q$ equal to a normalized total norm $\|x+y+z\|_p$ is used as an upper bound on the ratio of the triple deficit to the pair-deficit sum of a normalized triple $x,y,z$. Because $f_p$ is antitone, a lower bound on $q$ then yields an upper bound on that ratio via $f_p(q)$; comparing this against the value of $f_p$ at a fixed reference point is what confines a hypothetical strict counterexample's normalized total norm to a range below that reference point.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/ScalarEnvelope.lean#L59-L87

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_ScalarBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Function
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.NormPow
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sign.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Topology.Instances.Sign
import Mathlib.Topology.Order.Compact

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-! # Monotonicity of the scalar envelope -/

open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalConstruction.antitoneOn_scalarEnvelope {p : ℝ} (hp : 1 ≤ p) :
    AntitoneOn (scalarEnvelope p) (Set.Ico 0 1) := by sorry
