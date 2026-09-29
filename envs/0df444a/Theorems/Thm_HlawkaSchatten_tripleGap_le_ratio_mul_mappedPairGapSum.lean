-- Prove2me | Theorems.Thm_HlawkaSchatten_tripleGap_le_ratio_mul_mappedPairGapSum
-- name    : HlawkaSchatten.tripleGap_le_ratio_mul_mappedPairGapSum
-- status  : Proved
-- author  : @savarin
-- created : 2026-09-27T17:25:35.466746+00:00
-- url     : https://prove2.me/theorems/8aae59f2-db98-4a20-8fa5-dce39b353ea7
-- title:
--   Ordered-algebraic transfer of a Hlawka-type inequality through a model functional
-- statement:
--   Let $E$ be a type with an addition operation (no norm is assumed on $E$), and let $H$ be a normed additive commutative group (no inner product is assumed on $H$). Let $\mathrm{size},\mathrm{modelSize}:E\to\mathbb R$ be two real-valued functionals on $E$, and let $\mathrm{map}:E\to H$ be any function (not assumed linear or continuous). For a functional $s:E\to\mathbb R$ and $u,v\in E$ (respectively $u,v,w\in E$), write the *pair deficit* $\mathrm{pgap}(s)(u,v)=s(u)+s(v)-s(u+v)$ and the *triple deficit* $\mathrm{tgap}(s)(u,v,w)=s(u)+s(v)+s(w)-s(u+v+w)$ (`pairGap`, `tripleGap`), and $\mathrm{pgapsum}(s)(u,v,w)$ for the sum of the three pair deficits of $u,v,w$ (`pairGapSum`). Define the analogous *mapped pair deficit* $\mathrm{mpgap}(u,v)=\mathrm{modelSize}(u)+\mathrm{modelSize}(v)-\|\mathrm{map}(u)+\mathrm{map}(v)\|$, using the norm of $H$ on the mapped term, and likewise the mapped triple deficit $\mathrm{mtgap}$ and mapped pair-deficit sum $\mathrm{mpgapsum}$ (`mappedTripleGap`, `mappedPairGap`, `mappedPairGapSum`).
--
--   Fix $x,y,z\in E$ and real numbers $m>0$, $M\ge0$. Suppose:
--
--   1. (triple upper bound) $\mathrm{tgap}(\mathrm{size})(x,y,z) \le 2M\cdot\mathrm{mtgap}(x,y,z)$;
--   2. (pair lower bounds) $2m\cdot\mathrm{mpgap}(x,y)\le\mathrm{pgap}(\mathrm{size})(x,y)$, and likewise for the pairs $(x,z)$ and $(y,z)$;
--   3. (model Hlawka inequality) $\mathrm{mtgap}(x,y,z)\le\mathrm{mpgapsum}(x,y,z)$.
--
--   Then
--
--   $$
--   \mathrm{tgap}(\mathrm{size})(x,y,z) \;\le\; \frac{M}{m}\,\mathrm{pgapsum}(\mathrm{size})(x,y,z).
--   $$
--
--   This is the final, purely ordered-algebraic assembly step of the Bregman–Mazur route to a dimension-independent Hlawka constant: given a triple upper bound and three pair lower bounds relating the true deficits of $\mathrm{size}$ to their mapped, model counterparts, together with a Hlawka-type inequality already established for the model, the two factors of $2$ cancel exactly and only the ratio $M/m$ survives as the constant for $\mathrm{size}$.
--
--   **Formalization Note** The mapped quantities use only the norm of $H$, so the theorem needs $H$ to be a normed additive commutative group and nothing more — no inner product, and $\mathrm{map}$ need not be linear or continuous.
-- source:
--   https://github.com/savarin/hlawka-schatten/blob/79aa498bfcf7b22bd91d771fb32ec278e2d4704b/HlawkaSchatten/MazurGapComparison.lean#L52-L83

import Definitions.Def_HlawkaSchatten_GapComparison
import Definitions.Def_HlawkaSchatten_MazurGapComparison
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Dual

/-
Copyright (c) 2026 Ezzeri Esa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ezzeri Esa
-/

/-!
# Gap comparison through a nonlinear Mazur map

The Mazur map is not additive, so the Hilbert model for a family
`x, y, z` must use sums of the three *images*, rather than the image of
`x + y + z`.  This file records that distinction in the interface used by
the variational proof and carries out the final ordered-algebraic transfer.
-/


variable {E H : Type*} [Add E]
  {𝕜 : Type*} [RCLike 𝕜]
  [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]







include 𝕜

open HlawkaSchatten

omit 𝕜 in

theorem HlawkaSchatten.tripleGap_le_ratio_mul_mappedPairGapSum
    (size : E → ℝ) (modelSize : E → ℝ) (map : E → H)
    (m M : ℝ) (x y z : E)
    (hm : 0 < m) (hM : 0 ≤ M)
    (hTriple : tripleGap size x y z ≤
      2 * M * mappedTripleGap modelSize map x y z)
    (hPairXY : 2 * m * mappedPairGap modelSize map x y ≤ pairGap size x y)
    (hPairXZ : 2 * m * mappedPairGap modelSize map x z ≤ pairGap size x z)
    (hPairYZ : 2 * m * mappedPairGap modelSize map y z ≤ pairGap size y z)
    (hModel : mappedTripleGap modelSize map x y z ≤
      mappedPairGapSum modelSize map x y z) :
    tripleGap size x y z ≤ (M / m) * pairGapSum size x y z := by sorry
