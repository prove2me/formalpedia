-- Prove2me | Theorems.Thm_ModularCurve_JZero_exists_ord_div_sub_evalAt_eq_one
-- name    : ModularCurve.JZero.exists_ord_div_sub_evalAt_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/a59d168b-8a11-5801-8317-0d49cf42c25d
-- title:
--   At each place a normalised coordinate is a local parameter
-- statement:
--   Let $N\ge 1$ and let $F$ denote `modularFunctionFieldBar N`, the subfield of the Laurent series field over $\overline{\mathbb Q}$ generated over $\overline{\mathbb Q}$ by the coefficientwise image of the field $\mathbb Q(\mathrm{divisorExpansions}\,N)\subseteq\mathbb Q((q))$. Let $r\in\mathbb N$ and let $s\colon \mathrm{Fin}\,r\to F$ be a family satisfying `IsEmbBasis N s`, that is: the $s_j$ are linearly independent over $\overline{\mathbb Q}$ and their span is the Riemann–Roch space $\{f\in F \mid v(f)\le \exp(D(v))\text{ for every place }v\}$ attached to the divisor $D=(\mathrm{embDegree}\,N)\cdot[\mathrm{cuspInftyBar}\,N]$, a multiple of the cusp at infinity. Let $w$ be a place of $F$ over $\overline{\mathbb Q}$, i.e. a proper valuation subring of $F$ containing the image of $\overline{\mathbb Q}$ and which is a principal ideal ring, and write $\mathrm{ord}_w$ for the associated normalised integer valuation. Let $i$ be an index at which $\mathrm{ord}_w(s_i)$ is minimal among all $\mathrm{ord}_w(s_j)$. Then there is an index $j$ with $$\mathrm{ord}_w\bigl(s_j s_i^{-1}-\bigl(w.\mathrm{evalAt}(s_j s_i^{-1})\bigr)\bigr)=1,$$ where $w.\mathrm{evalAt}(f)\in\overline{\mathbb Q}$ is the residue of $f$ at $w$ read back through a left inverse of $\overline{\mathbb Q}\to$ (residue field of $w$), and is then mapped back into $F$ by the structure map. In words: for some $j$ the normalised coordinate $s_j/s_i$ minus its value at $w$ is a uniformiser at $w$.
--
--   This is the local form of the classical statement that a complete linear system of degree at least $2g+1$ embeds a curve, so that the resulting projective model is an immersion at every point: in an affine chart obtained by dividing by a coordinate of least order, one of the remaining coordinates serves as a local parameter. It is used to produce charts at places of $X_0(N)$ over $\overline{\mathbb Q}$, feeding the construction of local coordinates with non-vanishing derivative; the proof invokes [`ModularCurve.JZero.exists_regVal_chord_ne_zero`](thm.html#ModularCurve.JZero.exists_regVal_chord_ne_zero) together with the fact that every place of `modularFunctionFieldBar N` has residue degree one.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_exists_ord_div_sub_evalAt_eq_one.lean

import Definitions.Def_ModularCurve_JZeroHeightForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.exists_ord_div_sub_evalAt_eq_one (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (w : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N))
    (i : Fin r) (hi : ∀ j, w.ord (s i) ≤ w.ord (s j)) :
    ∃ j, w.ord (s j * (s i)⁻¹
      - algebraMap (AlgebraicClosure ℚ) (modularFunctionFieldBar N) (w.evalAt (s j * (s i)⁻¹))) = 1 := by sorry
