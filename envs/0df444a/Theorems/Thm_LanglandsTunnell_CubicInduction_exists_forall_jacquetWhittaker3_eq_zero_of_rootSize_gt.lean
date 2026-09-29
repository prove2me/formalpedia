-- Prove2me | Theorems.Thm_LanglandsTunnell_CubicInduction_exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt
-- name    : LanglandsTunnell.CubicInduction.exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:30:04.547556+00:00
-- url     : https://prove2.me/theorems/8460d099-57a4-519d-8464-abc597287e7c
-- title:
--   Vanishing of GL₃ cell-section Whittaker functions outside a cone
-- statement:
--   Let $v$ be a nonzero prime of the ring of integers of $\mathbb{Q}$, so that $\mathbb{Q}_v$ denotes the $v$-adic completion. Let $\chi = (\chi_0,\chi_1,\chi_2)$ be a triple of group homomorphisms $\mathbb{Q}_v^\times \to \mathbb{C}^\times$, each locally constant, and assume the product character $\chi_0\chi_1\chi_2$ is unitary, i.e. $\lVert(\chi_0\chi_1\chi_2)(u)\rVert = 1$ for every $u \in \mathbb{Q}_v^\times$. Let $\Phi : \mathbb{Q}_v^3 \to \mathbb{C}$ be locally constant with compact support. Consider the function $g \mapsto$ `jacquetWhittaker3 v χ Φ g`, the stabilised truncated Jacquet integral (`jacquetTruncated3` at the level `jacquetLevel`) of the right translate by $g$, under `gl3AmbientRightTranslate`, of the cell section `cellSectionOf v χ Φ`, namely the indicator function of the big cell `bigCell3` times $h \mapsto$ `cellValue v χ h` $\cdot\, \Phi(\,$`cellRatio v h`$)$. For $k \in \mathrm{GL}_3(\mathbb{Q}_v)$ put $\mathrm{d}(k) = \lVert \det k\rVert$, let $L(k)$ be the maximum of the norms of the three entries $k_{2,0}, k_{2,1}, k_{2,2}$ of the last row, and let $M(k)$ be the maximum of the norms of the three $2\times 2$ minors $k_{1,j}k_{2,j'} - k_{1,j'}k_{2,j}$ of the bottom two rows, for $(j,j') \in \{(0,1),(0,2),(1,2)\}$. The assertion is that there exists a real number $B$ such that for every $g \in \mathrm{GL}_3(\mathbb{Q}_v)$ for which the conjunction $\mathrm{d}(g)L(g)/M(g)^2 \le B$ and $M(g)/L(g)^2 \le B$ fails, one has `jacquetWhittaker3 v χ Φ g` $= 0$.
--
--   This is the support bound for the Whittaker function attached to a principal-series cell section on $\mathrm{GL}_3$ over a $v$-adic field: away from the cone cut out in the two simple-root sizes $\mathrm{d}(g)L(g)/M(g)^2$ and $M(g)/L(g)^2$ the Whittaker function vanishes identically. It feeds the gauge and admissibility estimates for local Whittaker functions in the cubic-induction part of the argument, being used in [`LanglandsTunnell.CubicInduction.exists_detTwist_jacquetWhittaker3_translate_whittaker_smooth_central_admissible_gauge`](thm.html#LanglandsTunnell.CubicInduction.exists_detTwist_jacquetWhittaker3_translate_whittaker_smooth_central_admissible_gauge), in [`LanglandsTunnell.CubicInduction.exists_forall_le_exists_localWhittaker_saturated_and_laurent_fe_of_mem_bad`](thm.html#LanglandsTunnell.CubicInduction.exists_forall_le_exists_localWhittaker_saturated_and_laurent_fe_of_mem_bad) and in [`LanglandsTunnell.CubicInduction.exists_gauge_of_mem_gl3CyclicSubspace_coefficientFn_principalSeries3`](thm.html#LanglandsTunnell.CubicInduction.exists_gauge_of_mem_gl3CyclicSubspace_coefficientFn_principalSeries3).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_LanglandsTunnell_CubicInduction_exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt.lean

import Definitions.Def_LanglandsTunnell_CubicInduction_JacquetWhittaker
import Definitions.Def_LanglandsTunnell_CubicInduction_MirabolicMajorant

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open IsDedekindDomain NumberField

theorem LanglandsTunnell.CubicInduction.exists_forall_jacquetWhittaker3_eq_zero_of_rootSize_gt
    (v : HeightOneSpectrum (𝓞 ℚ))
    (χ : Fin 3 → ((v.adicCompletion ℚ)ˣ →* ℂˣ)) (hχ : ∀ i, IsLocallyConstant (χ i))
    (hωu : ∀ u : (v.adicCompletion ℚ)ˣ, ‖(((χ 0 * χ 1 * χ 2) u : ℂˣ) : ℂ)‖ = 1)
    (Φ : (Fin 3 → v.adicCompletion ℚ) → ℂ) (hΦ : IsLocallyConstant Φ) (hΦc : HasCompactSupport Φ) :
    ∃ B : ℝ, ∀ g : LocalGL3 v,
      ¬ (detSize g * lastRowSup g / minorSup g ^ 2 ≤ B ∧ minorSup g / lastRowSup g ^ 2 ≤ B) →
        jacquetWhittaker3 v χ Φ g = 0 := by sorry
