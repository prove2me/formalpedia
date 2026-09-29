-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalConstruction_cyclicConstant_le_of_complex_constant
-- name    : HlawkaSchatten.DiagonalConstruction.cyclicConstant_le_of_complex_constant
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-28T18:58:34.297273+00:00
-- url     : https://prove2.me/theorems/ac90dc0a-6fc9-4328-bd21-da91445892b9
-- title:
--   The cyclic candidate $K_p$ is a necessary lower bound in dimension at least three
-- statement:
--   Let $n\ge3$ be a natural number and $p>1$ a real exponent. Consider the coordinate $\ell^p$-norm on $n$-tuples of complex numbers, $\|x\|_p = \bigl(\sum_{i=1}^n |x_i|^p\bigr)^{1/p}$ for $x\in\mathbb C^n$. For $x,y,z\in\mathbb C^n$, call
--   $$
--   \mathrm{pairGap}(x,y)=\|x\|_p+\|y\|_p-\|x+y\|_p
--   $$
--   the pair deficit, $\mathrm{tripleGap}(x,y,z)=\|x\|_p+\|y\|_p+\|z\|_p-\|x+y+z\|_p$ the triple deficit, and $\mathrm{pairGapSum}(x,y,z)$ the sum of the three pair deficits over the pairs $\{x,y\},\{x,z\},\{y,z\}$. Call a real number $C$ an admissible Hlawka constant for $\|\cdot\|_p$ on $\mathbb C^n$ when
--   $$
--   \mathrm{tripleGap}(x,y,z)\;\le\;C\cdot\mathrm{pairGapSum}(x,y,z)
--   $$
--   holds for all $x,y,z\in\mathbb C^n$. Let
--   $$
--   R_p(t) \;=\; \frac{3A_p(t)-3^{1/p}|2-t|}{6A_p(t)-3B_p(t)}, \qquad A_p(t)=(t^p+2)^{1/p},\ B_p(t)=(2|1-t|^p+2^p)^{1/p},
--   $$
--   be the cyclic ratio (for $t\ge0$, $A_p(t)$ is the coordinate $p$-norm of each of $(-t,1,1),(1,-t,1),(1,1,-t)\in\mathbb R^3$ and $B_p(t)$ that of each of their pairwise sums), and let
--   $$
--   K_p \;=\; \sup\{\,R_p(t) : 1/2\le t\le2\,\}
--   $$
--   be the cyclic candidate constant.
--
--   The theorem states: if $C$ is any admissible Hlawka constant for $\|\cdot\|_p$ on $\mathbb C^n$ with $n\ge3$, then
--   $$
--   K_p \;\le\; C.
--   $$
--
--   This is the necessity half of sharpness for the diagonal construction. A separate theorem shows $K_p$ is itself admissible for complex diagonal triples in every finite dimension, for every real $p\ge256$. Combining the two: for $p\ge256$, $K_p$ is the sharp dimension-independent Hlawka constant for $\|\cdot\|_p$ on $\mathbb C^n$, $n\ge3$; this theorem alone, valid for every real $p>1$, only shows that no constant smaller than $K_p$ can work, and does not by itself establish admissibility or exact sharpness outside the range where the companion theorem is proved.
--
--   **Formalization Note.** This theorem is stated for the coordinate norm $\|\cdot\|_p$ on $\mathbb C^n$ directly. A separate theorem (`schattenPNorm_diagonal`) identifies $\|\cdot\|_p$ with the Schatten $p$-norm of a diagonal operator on $\mathbb C^n$; that identification is not needed to state or prove this theorem.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/CyclicWitness.lean#L111-L119

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Basic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_GapComparison
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Data.Fin.VecNotation
import Mathlib.Topology.Order.Compact

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Cyclic witnesses and the necessary lower bound

The three cyclic vectors have equal norms and their ratio is the scalar
formula defining the comparison constant. Zero padding preserves all seven
norms, so the lower bound holds in every dimension at least three.
-/

open HlawkaSchatten
open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalConstruction.cyclicConstant_le_of_complex_constant {p C : ℝ} (hp : 1 < p)
    {n : ℕ} (hn : 3 ≤ n)
    (hC : HasHlawkaConstant (lpNorm p : (Fin n → ℂ) → ℝ) C) :
    cyclicConstant p ≤ C := by sorry
