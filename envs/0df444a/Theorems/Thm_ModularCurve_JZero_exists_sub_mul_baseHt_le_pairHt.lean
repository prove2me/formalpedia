-- Prove2me | Theorems.Thm_ModularCurve_JZero_exists_sub_mul_baseHt_le_pairHt
-- name    : ModularCurve.JZero.exists_sub_mul_baseHt_le_pairHt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/6584808c-2dc3-54cb-a71d-3575467de547
-- title:
--   Lower bound for pair heights against a fixed place
-- statement:
--   Let $N$ be a nonzero natural number and let $F =$ `modularFunctionFieldBar N`, the subfield of the Laurent series field over $\overline{\mathbb{Q}}$ generated over $\overline{\mathbb{Q}}$ by the coefficientwise image of the full level-$N$ modular function field; places are taken in the project's sense, namely valuation subrings of $F$ containing the image of $\overline{\mathbb{Q}}$, different from $F$ itself, and principal ideal rings. Let $s : \mathrm{Fin}\, r \to F$ be an embedding basis in the sense of `IsEmbBasis N s`: the family $s$ is linearly independent over $\overline{\mathbb{Q}}$ and its span is the Riemann–Roch space of the divisor $(\mathrm{embDegree}\,N)\cdot[\,\overline{\infty}\,]$, where $\overline{\infty} =$ `cuspInftyBar N` is the $q$-adic place at infinity. For a real $\varepsilon > 0$ and a place $w_0$ of $F$, the assertion is the existence of a real constant $C$ such that every place $u$ with $u \neq w_0$ and $u \neq \overline{\infty}$ satisfies $$(1-\varepsilon)\,\mathrm{baseHt}\,s\,\overline{\infty}\,u - C \le \mathrm{pairHt}\,s\,u\,w_0,$$ where $\mathrm{pairHt}\,s\,v\,w = \mathrm{pointHt}\,s\,v + \mathrm{pointHt}\,s\,w - \mathrm{absLogHeight}(\mathrm{chordVec}\,s\,v\,w)$ is built from the normalised absolute logarithmic heights of the evaluation vectors of $s$ and of the chord vector, and $\mathrm{baseHt}\,s\,b\,v$ is $0$ if $v = b$ and $\mathrm{pairHt}\,s\,v\,b$ otherwise.
--
--   This is the lower-bound half of the comparison, up to $\varepsilon$ and a constant, between the Weil height attached to a fixed degree-one place $w_0$ and the one attached to the cusp $\overline{\infty}$, the two divisors having the same degree. It is used for auxiliary points in the lower bounds for the height form on $\mathrm{JZero}\,N$, being cited by [`ModularCurve.JZero.exists_baseMass_le_heightForm_of_exists_two_le`](thm.html#ModularCurve.JZero.exists_baseMass_le_heightForm_of_exists_two_le) and [`ModularCurve.JZero.exists_sum_pairHt_le_of_forall_le_one`](thm.html#ModularCurve.JZero.exists_sum_pairHt_le_of_forall_le_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_exists_sub_mul_baseHt_le_pairHt.lean

import Definitions.Def_ModularCurve_JZeroHeightForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve ModularCurve

theorem ModularCurve.JZero.exists_sub_mul_baseHt_le_pairHt (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s)
    (ε : ℝ) (hε : 0 < ε)
    (w₀ : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N)) :
    ∃ C : ℝ, ∀ u : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
      u ≠ w₀ → u ≠ cuspInftyBar N →
        (1 - ε) * baseHt s (cuspInftyBar N) u - C ≤ pairHt s u w₀ := by sorry
