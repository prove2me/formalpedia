-- Prove2me | Theorems.Thm_ModularCurve_JZero_exists_pointHt_le_absLogHeight_jCoord
-- name    : ModularCurve.JZero.exists_pointHt_le_absLogHeight_jCoord
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:41.339792+00:00
-- url     : https://prove2.me/theorems/7efe8414-6c2f-542b-8263-f1f3edb07a09
-- title:
--   Point heights bounded linearly by the j-coordinate height
-- statement:
--   Fix a nonzero level $N$ and let $\bar M_N$ denote `modularFunctionFieldBar N`, the base change to $\overline{\mathbb{Q}}$ of the full level-$N$ modular function field inside $\mathrm{LaurentSeries}(\overline{\mathbb{Q}})$. Let $r$ be a natural number and $s : \mathrm{Fin}\,r \to \bar M_N$ a family satisfying `IsEmbBasis N s`, that is: $s$ is linearly independent over $\overline{\mathbb{Q}}$ and its span is the Riemann–Roch space $\{f : v(f) \le \exp(D(v))$ for all places $v\}$ of the divisor $D = (\mathrm{embDegree}\,N)\cdot[\mathrm{cuspInftyBar}\,N]$. The assertion is that there exist real constants $B_s, C_s \ge 0$ such that for every place $v$ of $\bar M_N$ over $\overline{\mathbb{Q}}$ (a proper valuation subring containing the image of $\overline{\mathbb{Q}}$, with principal ideals) at which the element $j$ of $\bar M_N$ — the coefficientwise image of the $q$-expansion `jq` $= q^{-1}\cdot jNumQ$ — satisfies $\mathrm{ord}_v(j) \ge 0$, one has $$\mathrm{pointHt}_s(v) \;\le\; B_s \cdot \mathrm{absLogHeight}\,[\,\mathrm{jCoord}\,N\,v,\;1\,] + C_s .$$ Here $\mathrm{pointHt}_s(v)$ is the absolute logarithmic height of the tuple $\bigl(v\text{-value of } s_i \cdot s_{\mathrm{pivot}}^{-1}\bigr)_i$ (zero if $r = 0$), $\mathrm{jCoord}\,N\,v$ is a chosen $c \in \overline{\mathbb{Q}}$ with $\mathrm{ord}_v(j - c) > 0$, and $\mathrm{absLogHeight}$ is the logarithmic height of a tuple divided by the degree over $\mathbb{Q}$ of the field it generates.
--
--   This is the per-place comparison between the height of a point of the modular curve of level $N$, measured through an embedding basis of the Riemann–Roch space of a multiple of the cusp, and the naive height of its $j$-coordinate, at places where $j$ is integral. It is used in [`ModularCurve.JZero.ptsum_pointHt_le_divNaiveHeight`](thm.html#ModularCurve.JZero.ptsum_pointHt_le_divNaiveHeight), where the bound is summed over the places occurring in a divisor.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ModularCurve_JZero_exists_pointHt_le_absLogHeight_jCoord.lean

import Definitions.Def_ModularCurve_JZeroNaiveHeight
import Definitions.Def_ModularCurve_JZeroHeightForm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve in

theorem ModularCurve.JZero.exists_pointHt_le_absLogHeight_jCoord (N : ℕ) [NeZero N] {r : ℕ}
    (s : Fin r → modularFunctionFieldBar N) (hs : IsEmbBasis N s) :
    ∃ Bs Cs : ℝ, 0 ≤ Bs ∧ 0 ≤ Cs ∧
      ∀ v : Place (AlgebraicClosure ℚ) (modularFunctionFieldBar N),
        0 ≤ v.ord (⟨coeffEmb (AlgebraicClosure ℚ) jq,
          coeffEmb_mem_laurentBaseChange (AlgebraicClosure ℚ) (jq_mem_full N)⟩ :
            modularFunctionFieldBar N) →
        pointHt s v ≤ Bs * absLogHeight ![jCoord N v, 1] + Cs := by sorry
