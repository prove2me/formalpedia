-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalConstruction_cyclicConstant_le_exponent
-- name    : HlawkaSchatten.DiagonalConstruction.cyclicConstant_le_exponent
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-28T17:56:14.144369+00:00
-- url     : https://prove2.me/theorems/1f839976-781f-423d-89d3-9baefc829cce
-- title:
--   A rough exponent bound $K_p\le p$ for the cyclic candidate constant
-- statement:
--   For a real exponent $p$ and $t\ge0$, let $A_p(t)=(t^p+2)^{1/p}$, $B_p(t)=(2|1-t|^p+2^p)^{1/p}$, and
--   $$
--   R_p(t) \;=\; \frac{3A_p(t)-3^{1/p}|2-t|}{6A_p(t)-3B_p(t)}
--   $$
--   be the cyclic ratio built from the cyclic vectors $(-t,1,1),(1,-t,1),(1,1,-t)$ and their pairwise sums. Let
--   $$
--   K_p \;=\; \sup\{R_p(t) : 1/2\le t\le2\}
--   $$
--   be the cyclic candidate constant. Here, for a finite index set $\iota$ and $x:\iota\to\mathbb R$, $\|x\|_p=\bigl(\sum_i|x_i|^p\bigr)^{1/p}$ is the coordinate $p$-norm, and for $t\ge0$, $A_p(t)$ is the value of $\|\cdot\|_p$ on each cyclic vector and $B_p(t)$ its value on each of their pairwise sums. For $x,y,z:\iota\to\mathbb R$ let $\mathrm{tripleGap}(x,y,z)=\|x\|_p+\|y\|_p+\|z\|_p-\|x+y+z\|_p$ be the triple deficit, and $\mathrm{pairGapSum}(x,y,z)$ the sum of the three pair deficits $\|u\|_p+\|v\|_p-\|u+v\|_p$ over $\{u,v\}=\{x,y\},\{x,z\},\{y,z\}$. A real $C$ is an admissible Hlawka constant for $\|\cdot\|_p$ when $\mathrm{tripleGap}(x,y,z)\le C\cdot\mathrm{pairGapSum}(x,y,z)$ for all $x,y,z$.
--
--   The theorem states that for every real exponent $p>1$,
--   $$
--   K_p \;\le\; p.
--   $$
--
--   This is a coarse, purely exponent-dependent upper bound on $K_p$, valid for every real $p>1$. It complements the separate results that $K_p$ is admissible for complex diagonal triples in every finite dimension when $p\ge256$ and that every admissible constant in some dimension $n\ge3$ is at least $K_p$.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/ScalarEnvelope.lean#L13-L16

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
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

theorem HlawkaSchatten.DiagonalConstruction.cyclicConstant_le_exponent {p : ℝ} (hp : 1 < p) : cyclicConstant p ≤ p := by sorry
