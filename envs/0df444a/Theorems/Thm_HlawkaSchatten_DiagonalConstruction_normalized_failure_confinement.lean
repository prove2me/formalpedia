-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalConstruction_normalized_failure_confinement
-- name    : HlawkaSchatten.DiagonalConstruction.normalized_failure_confinement
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-28T18:39:14.629019+00:00
-- url     : https://prove2.me/theorems/25486548-1609-4de3-8b10-a65e06a7d88b
-- title:
--   Scalar confinement of a normalized strict Hlawka failure, for $p\ge256$
-- statement:
--   Let $\iota$ be a finite index set and $p\ge256$. For $t\in[1/2,2]$ define
--
--   $$
--   A_p(t)=(t^p+2)^{1/p},\qquad B_p(t)=\big(2|1-t|^p+2^p\big)^{1/p},\qquad R_p(t)=\frac{3A_p(t)-3^{1/p}|2-t|}{6A_p(t)-3B_p(t)},
--   $$
--
--   and let $K_p = \sup\{R_p(t): t\in[1/2,2]\}$ be the cyclic constant (proved sharp for complex diagonal triples, in every finite dimension at least three, once $p\ge256$, by other theorems not used on this page). For $x,y,z:\iota\to\mathbb R$ write $\|v\|_p=\big(\sum_i|v_i|^p\big)^{1/p}$, and suppose:
--
--   1. the singleton norms already sum to one, $\|x\|_p+\|y\|_p+\|z\|_p=1$;
--   2. the total-sum norm dominates each singleton norm, $\|x\|_p\le\|x+y+z\|_p$, $\|y\|_p\le\|x+y+z\|_p$, $\|z\|_p\le\|x+y+z\|_p$;
--   3. $(x,y,z)$ is a strict failure of the $K_p$-Hlawka inequality:
--   $$
--   (2K_p-1)+\|x+y+z\|_p-K_p\big(\|x+y\|_p+\|x+z\|_p+\|y+z\|_p\big)<0
--   $$
--   (using Hypothesis 1 to write the singleton-norm sum as $1$).
--
--   Then the total-sum norm, the sum of the three pairwise deficits, and the three singleton norms are all confined to explicit narrow ranges:
--
--   $$
--   \tfrac13 \le \|x+y+z\|_p < \tfrac{53}{150},
--   $$
--   $$
--   \big(\|x\|_p+\|y\|_p-\|x+y\|_p\big)+\big(\|x\|_p+\|z\|_p-\|x+z\|_p\big)+\big(\|y\|_p+\|z\|_p-\|y+z\|_p\big) < \tfrac2p,
--   $$
--   $$
--   \tfrac{22}{75}<\|x\|_p<\tfrac{53}{150},\qquad \tfrac{22}{75}<\|y\|_p<\tfrac{53}{150},\qquad \tfrac{22}{75}<\|z\|_p<\tfrac{53}{150}.
--   $$
--
--   This converts the linear growth rate of $K_p$ into concrete numeric bounds — total norm just above $1/3$, singleton norms clustered near $1/3$, and a pair-deficit sum shrinking like $1/p$ — that are exactly the data the later coordinate-geometry arguments of the sharp diagonal construction take as their starting hypotheses.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/Confinement.lean#L73-L97

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Normalization
import Definitions.Def_HlawkaSchatten_GapComparison
import Mathlib.Analysis.Complex.ExponentialBounds
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
import Mathlib.Tactic.Abel
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

/-! # Scalar confinement of a normalized strict counterexample -/


variable {ι : Type*} [Fintype ι]

open HlawkaSchatten
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalConstruction.normalized_failure_confinement {p : ℝ} (hp : 256 ≤ p)
    (x y z : ι → ℝ) (hS : lpNorm p x + lpNorm p y + lpNorm p z = 1)
    (hx : lpNorm p x ≤ lpNorm p (x + y + z))
    (hy : lpNorm p y ≤ lpNorm p (x + y + z))
    (hz : lpNorm p z ≤ lpNorm p (x + y + z))
    (hf : hlawkaDeficit p (cyclicConstant p) x y z < 0) :
    (1 / 3 ≤ lpNorm p (x + y + z) ∧ lpNorm p (x + y + z) < 53 / 150) ∧
      pairGapSum (lpNorm p) x y z < 2 / p ∧
      (22 / 75 < lpNorm p x ∧ lpNorm p x < 53 / 150) ∧
      (22 / 75 < lpNorm p y ∧ lpNorm p y < 53 / 150) ∧
      (22 / 75 < lpNorm p z ∧ lpNorm p z < 53 / 150) := by sorry
