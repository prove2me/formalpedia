-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalConstruction_exists_failure_in_entryBox
-- name    : HlawkaSchatten.DiagonalConstruction.exists_failure_in_entryBox
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-28T18:42:14.088983+00:00
-- url     : https://prove2.me/theorems/1b70fa77-403d-4b07-84d9-c01207876485
-- title:
--   Localizing a Hlawka failure to the cyclic coordinate box
-- statement:
--   For $p>0$ and $x:\{0,1,2\}\to\mathbb R$, write $\mathrm{lpNorm}_p(x):=\bigl(\sum_i|x_i|^p\bigr)^{1/p}$ for the finite coordinate $p$-norm. For $K\in\mathbb R$ and $x,y,z:\{0,1,2\}\to\mathbb R$, let
--   $$\mathrm{hlawkaDeficit}_{p,K}(x,y,z):=(2K-1)\bigl(\mathrm{lpNorm}_p(x)+\mathrm{lpNorm}_p(y)+\mathrm{lpNorm}_p(z)\bigr)+\mathrm{lpNorm}_p(x+y+z)-K\bigl(\mathrm{lpNorm}_p(x+y)+\mathrm{lpNorm}_p(x+z)+\mathrm{lpNorm}_p(y+z)\bigr).$$
--   Writing $\mathrm{pairGap}(N)(a,b):=N(a)+N(b)-N(a+b)$, $\mathrm{tripleGap}(N)(a,b,c):=N(a)+N(b)+N(c)-N(a+b+c)$, and $\mathrm{pairGapSum}(N)(a,b,c)$ for the sum of the three pair gaps, one has $\mathrm{hlawkaDeficit}_{p,K}(x,y,z)=K\cdot\mathrm{pairGapSum}(\mathrm{lpNorm}_p)(x,y,z)-\mathrm{tripleGap}(\mathrm{lpNorm}_p)(x,y,z)$, which is $\ge0$ for all $x,y,z$ exactly when $\mathrm{lpNorm}_p$ has Hlawka constant $K$; so a **negative** value of $\mathrm{hlawkaDeficit}_{p,K}$ is a strict failure of that inequality at $(x,y,z)$.
--
--   Write a *triple* $X$ as three columns $X_0,X_1,X_2\in\mathbb R^3$, with $X_{j,i}$ coordinate $i$ of column $j$ (Lean: `X j i`), and let $\mathrm{tripleDeficit}_{p,K}(X):=\mathrm{hlawkaDeficit}_{p,K}(X_0,X_1,X_2)$. Let $\mathrm{cyclicCenter}$ be the triple whose $j$-th column has $-1$ in position $j$ and $1$ elsewhere, and let $\mathrm{entryBox}:=\{X:|X_{j,i}-\mathrm{cyclicCenter}_{j,i}|\le19/100\text{ for all }j,i\}$.
--
--   Let
--   $$
--   \begin{gathered}
--   K_p:=\mathrm{cyclicConstant}(p):=\sup\{R_p(t):1/2\le t\le2\},\quad R_p(t):=\frac{3A_p(t)-3^{1/p}|2-t|}{6A_p(t)-3B_p(t)}, \\
--   \quad A_p(t):=(t^p+2)^{1/p},\ B_p(t):=\bigl(2|1-t|^p+2^p\bigr)^{1/p}.
--   \end{gathered}
--   $$
--
--   For every $p\ge256$ and every $x,y,z:\{0,1,2\}\to\mathbb R$ with $\mathrm{hlawkaDeficit}_{p,K_p}(x,y,z)<0$, this theorem produces a triple $X\in\mathrm{entryBox}$ that is still a strict failure:
--   $$\mathrm{tripleDeficit}_{p,K_p}(X)<0.$$
--
--   This localizes an arbitrary strict counterexample — after normalizing its total mass, relabeling which vector plays which coordinate role together with a sign flip per coordinate, and rescaling by $3$ — into the fixed box of triples within $19/100$ of the cyclic sign pattern. Turning an otherwise unbounded search for failures of the Hlawka inequality into one confined to a small, fixed region is what makes the region's own geometry (its convexity, and the curvature of the deficit on it) usable against the failure.
--
--   **Formalization Note** The box radius $19/100$ is the exact entrywise tolerance this construction's coordinate-geometry and curvature estimates are built around: the localization step used here puts the confined counterexample's entries within $6/50+84/(5p)$ of the cyclic pattern, which is $0.185625$ at $p=256$ — below $19/100=0.19$, but with little room to spare.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/Localization.lean#L69-L151

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Localization
import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Normalization
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

/-! # A strict counterexample lies in the cyclic coordinate box -/

open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalConstruction.exists_failure_in_entryBox {p : ℝ} (hp : 256 ≤ p)
    (x y z : Fin 3 → ℝ) (hf : hlawkaDeficit p (cyclicConstant p) x y z < 0) :
    ∃ X ∈ entryBox, tripleDeficit p (cyclicConstant p) X < 0 := by sorry
