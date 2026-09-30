-- Prove2me | Theorems.Thm_NonuniformCompetitive_Isosceles_ratio_increases_to_e_ratio
-- name    : NonuniformCompetitive.Isosceles.ratio_increases_to_e_ratio
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T10:55:57.321907+00:00
-- url     : https://prove2.me/theorems/a6ada6b9-2506-43e7-8352-6c1c82c82789
-- title:
--   §5, p. 566 — the ratio of Theorem 12 increases in $d$ and tends to $e/(e-1)$
-- statement:
--   For an integer $d\ge1$ let
--   $$\alpha_d=\frac{e_{2d-1}+1/4d}{(e_{2d-1}-1)+1/2d},\qquad e_{2d-1}=\left(\frac{2d}{2d-1}\right)^{2d-1}.$$
--   Then the sequence $\alpha_1,\alpha_2,\alpha_3,\dots$ is strictly increasing, and
--   $$\lim_{d\to\infty}\alpha_d=\frac{e}{e-1}.$$
--
--   Thus the optimal randomized two-server ratio on the $1$-$d$-$d$ triangle starts at $3/2$ (equilateral triangle, $d=1$) and approaches the optimal randomized ratio $e/(e-1)$ of ski-rental-type problems as the triangle becomes long and thin.
--
--   **Formalization Note** The paper says the ratio "grows"; this is read as strict increase, stated as strict monotonicity of $n\mapsto\alpha_{n+1}$ on $\mathbb N$. The limit is along $d\to\infty$ in $\mathbb N$ (the value at $d=0$ is irrelevant to it).
-- source:
--   Karlin, Manasse, McGeoch, Owicki, Competitive Randomized Algorithms for Nonuniform Problems, Algorithmica 11 (1994), DOI 10.1007/BF01189993, p. 566, §5, sentence after the proof of Theorem 12

import Mathlib
import Definitions.Def_NonuniformCompetitive_Isosceles_isoscelesRatio

namespace NonuniformCompetitive.Isosceles

/-- §5, p. 566 (Karlin–Manasse–McGeoch–Owicki 1994): the competitive ratio of Theorem 12 grows
and approaches `e/(e - 1)` as `d` grows. "Grows" is read as strictly increasing over the
admissible values `d = 1, 2, 3, …`, stated as strict monotonicity of `n ↦ isoscelesRatio (n + 1)`;
the limit is taken as `d → ∞`. -/
theorem ratio_increases_to_e_ratio :
    StrictMono (fun n : ℕ => isoscelesRatio (n + 1)) ∧
      Filter.Tendsto isoscelesRatio Filter.atTop
        (nhds (Real.exp 1 / (Real.exp 1 - 1))) := by sorry

end NonuniformCompetitive.Isosceles
