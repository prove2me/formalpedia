-- Prove2me | Theorems.Thm_HlawkaSchatten_DiagonalConstruction_cyclic_maximum_attained
-- name    : HlawkaSchatten.DiagonalConstruction.cyclic_maximum_attained
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-28T17:33:18.44708+00:00
-- url     : https://prove2.me/theorems/ca8c443f-df19-4ea8-bcb8-b244da724328
-- title:
--   Attainment of the cyclic candidate constant $K_p$
-- statement:
--   For a real exponent $p$ and $t\ge0$, let
--   $$
--   A_p(t)=(t^p+2)^{1/p}, \qquad B_p(t) = (2|1-t|^p+2^p)^{1/p}
--   $$
--   be the coordinate $p$-norms of the cyclic vectors $(-t,1,1),(1,-t,1),(1,1,-t)$ and of their pairwise sums, and define the cyclic ratio
--   $$
--   R_p(t) \;=\; \frac{3A_p(t) - 3^{1/p}|2-t|}{6A_p(t) - 3B_p(t)}.
--   $$
--   Define the cyclic candidate constant as the supremum of $R_p$ over the compact interval $t\in[1/2,2]$,
--   $$
--   K_p \;=\; \sup\{\,R_p(t) : 1/2\le t\le 2\,\}.
--   $$
--
--   The theorem states that for every real $p>1$ this supremum is attained: there is some $t_0\in[1/2,2]$ with $R_p(t_0)=K_p$.
--
--   $K_p$ enters the theory a priori only as a supremum, so later arguments need to know it is realized by an actual parameter value rather than merely approached. It sits alongside a separate theorem proving $K_p$ admissible for complex diagonal triples in every finite dimension when $p\ge256$, and a separate theorem (`cyclicConstant_le_of_complex_constant`) proving that no smaller constant works in any dimension at least three, for every real $p>1$. This attainment theorem itself holds for every real $p>1$ and does not by itself say anything about admissibility or sharpness; until combined with the $p\ge256$ admissibility theorem, $K_p$ should be read as the cyclic candidate constant — an explicit, attained real number — rather than as the already-established sharp diagonal Hlawka constant.
--
--   **Formalization Note.** Mathlib's `sSup` on the reals is a total function (it returns a default value on sets that are empty or unbounded above), so by itself `cyclicConstant p = sSup (...)` does not guarantee attainment. The mathematical content of this theorem is exactly that extra fact: the supremum here is attained by a point of $[1/2,2]$, not merely approached.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/DiagonalConstruction/Cyclic.lean#L93-L100

import Definitions.Def_HlawkaSchatten_DiagonalConstruction_Cyclic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.Compact

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# The cyclic comparison constant

The constant is defined from an explicit scalar formula on a fixed compact
interval. Its denominator is positive, so continuity gives an attained
maximum without presupposing the global Hlawka inequality.
-/

open HlawkaSchatten.DiagonalConstruction

theorem HlawkaSchatten.DiagonalConstruction.cyclic_maximum_attained {p : ℝ} (hp : 1 < p) :
    ∃ t ∈ Set.Icc (1 / 2 : ℝ) 2, cyclicRatio p t = cyclicConstant p := by sorry
